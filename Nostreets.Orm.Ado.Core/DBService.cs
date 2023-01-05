using Newtonsoft.Json;
using Newtonsoft.Json.Linq;
using Nostreets.Extensions.DataControl.Classes;
using Nostreets.Extensions.Extend.Basic;
using Nostreets.Extensions.Extend.Data;
using Nostreets.Extensions.Helpers.Data;
using Nostreets.Extensions.Helpers.Data.QueryProvider;
using Nostreets.Extensions.Interfaces;
using Nostreets.Extensions.Utilities;

using System;
using System.Collections;
using System.Collections.Generic;
using System.ComponentModel.DataAnnotations;
using System.ComponentModel.DataAnnotations.Schema;
using System.Data;
using System.Data.SqlClient;
using System.Dynamic;
using System.Linq;
using System.Reflection;

namespace Nostreets.Orm.Ado
{
    public class DBService : SqlService, IDBService
    {
        public DBService(Type type) : base()
        {
            try
            {
                SetUp(type);
            }
            catch (Exception ex)
            {
                LogThenThrow(ex);
            }
        }

        public DBService(Type type, string connectionKey) : base(connectionKey)
        {
            try
            {
                SetUp(type);
            }
            catch (Exception ex)
            {
                LogThenThrow(ex);
            }
        }

        public DBService(Type type, ORMOptions options) : base(options.ConnectionKey)
        {
            try
            {
                if (options.WipeDB && !ORMOptions.HasWipedDB)
                {
                    WipeDB();
                    ORMOptions.HasWipedDB = true;
                }

                SetUp(type, options);
            }
            catch (Exception ex)
            {
                LogThenThrow(ex);
            }
        }

        private IDBService<Error> _errorLog = null;
        private string _lastQueryExcuted = null;
        private List<EntityMap> _mappedEntities = null;

        private Dictionary<string, string> _partialProcs = null,
                                           _procTemplates = null;

        private bool _tableCreation = false,
                     _nullLock = false;

        private int _tableLayer = 0;
        private Type _type = null;

        internal Type IdType { get; private set; } = null;

        #region Internal Logic

        private void BackupAndDropType(EntityMap map)
        {
            EntityAssociation[] tblsTypeRefers = map.Association;
            IEnumerable<EntityMap> tblsThatReferType = _mappedEntities.Where(a => (a.Association.Length > 0 && a.Association.Any(b => b.Type == map.Type)) && a != map);

            if (tblsThatReferType != null && tblsThatReferType.Count() > 0)
                foreach (EntityMap tbl in tblsThatReferType)
                    if (!CheckIfBackUpExist(tbl.Type))
                        BackupAndDropType(tbl);

            CreateBackupTable(map.Type);
            DropTable(map.Type);
            DropProcedures(map.Type);

            if (tblsTypeRefers != null)
            {
                if (tblsTypeRefers.Any(a => a.Type.IsCollection()))
                    foreach (EntityAssociation list in tblsTypeRefers.Where(a => a.Type.IsCollection()))
                    {
                        CreateBackupTable(list.Type, map.Type.Name + "_");
                        DropTable(list.Type, map.Type.Name + "_");
                        DropProcedures(list.Type, map.Type.Name + "_");
                    }

                if (tblsTypeRefers.Any(a => a.Type.IsEnum))
                    foreach (EntityAssociation list in tblsTypeRefers.Where(a => a.Type.IsEnum))
                    {
                        DropTable(list.Type, map.Type.Name + "_");
                        DropProcedures(list.Type, map.Type.Name + "_");
                    }
            }
        }

        private void DeleteAllTablesOfType()
        {
            List<Type> tbls = _mappedEntities.Select(a => a.Type).ToList();

            for (int i = 0; i < tbls.Count; i++)
            {
                Type type = tbls[i];
                if (type.GetProperties().Length > 0 && type.GetProperties().Any(a => a.PropertyType.IsCollection()))
                {
                    PropertyInfo[] collections = type.GetProperties().Where(a => a.PropertyType.IsCollection()).ToArray();

                    foreach (PropertyInfo collection in collections)
                    {
                        string tblName = type.Name.SafeName();

                        DropTable(collection.PropertyType, tblName + '_' + collection.Name + '_');
                        DropBackupTable(collection.PropertyType, tblName + '_' + collection.Name + '_');
                        DropProcedures(collection.PropertyType, tblName + '_' + collection.Name + '_');

                        if (tbls.Contains(collection.PropertyType))
                            tbls.Remove(collection.PropertyType);
                    }
                }

                DropTable(type);
                DropBackupTable(type);
                DropProcedures(type);
            }
        }

        private void SetUpMappedTypes()
        {
            List<EntityMap> result = new List<EntityMap>();

            MapType(_type, ref result);

            _mappedEntities = result;
        }

        private string GetMappedTypesXML()
        {
            return _mappedEntities.XmlSerialize();
        }

        private object GetNormalizedSchema(Type type, string prefix = null)
        {
            List<Tuple<string, Type, Dictionary<Type, object[]>>> props = new List<Tuple<string, Type, Dictionary<Type, object[]>>>();
            List<Tuple<string, Type, MethodAttributes, List<Tuple<Type, ParameterAttributes>>, Dictionary<Type, object[]>>> methods =
                type.GetMethods().Select(
                    a =>
                    new Tuple<string, Type, MethodAttributes, List<Tuple<Type, ParameterAttributes>>, Dictionary<Type, object[]>>(
                          a.Name
                        , a.ReturnType
                        , a.Attributes
                        , a.GetParameters().Select(
                             b => new Tuple<Type, ParameterAttributes>(b.ParameterType, b.Attributes)).ToList()
                        , null
                    )).ToList();

            if (type.IsEnum)
            {
                props.AddRange(new Tuple<string, Type, Dictionary<Type, object[]>>[] {
                    new Tuple<string, Type, Dictionary<Type, object[]>>("Id", typeof(int), null),
                    new Tuple<string, Type, Dictionary<Type, object[]>>("Name", typeof(string), null),
                    new Tuple<string, Type, Dictionary<Type, object[]>>("Value", typeof(int), null)
                });
            }
            else if (!type.IsCollection())
            {
                if (NeedsIdProp(type, out int ordinal))
                    type = type.AddProperty(typeof(int), "Id");

                PropertyInfo[] baseProps = type.GetProperties();

                foreach (PropertyInfo prop in baseProps)
                {
                    if (ShouldNormalize(prop.PropertyType))
                    {
                        props.Add(new Tuple<string, Type, Dictionary<Type, object[]>>(prop.Name + "Id", typeof(int), null));
                    }
                    else if (!prop.PropertyType.IsCollection())
                    {
                        props.Add(new Tuple<string, Type, Dictionary<Type, object[]>>(prop.Name, prop.PropertyType, null));
                    }
                }
            }
            else
            {
                Type collectionType = type.GetTypeOfT();
                props.AddRange(new Tuple<string, Type, Dictionary<Type, object[]>>[]{
                    new Tuple<string, Type, Dictionary<Type, object[]>>(prefix?.Split('_')[0] + "Id", typeof(int), null),
                    new Tuple<string, Type, Dictionary<Type, object[]>>(collectionType.IsSystemType() ? "Serialized" + GetTableName(type) : collectionType.Name + "Id", collectionType.IsSystemType() ? typeof(string) : typeof(int), null)
                });
            }

            return ClassBuilder.CreateObject(type.Name, props, methods);
        }

        private List<PropertyInfo> GetPropsByAttribute<T>(Type type) where T : Attribute
        {
            return type.GetPropertiesByAttribute<T>() ?? new List<PropertyInfo>();
        }

        //private Type[] GetRelationships(Type type)
        //{
        //    if (type.IsCollection())
        //    {
        //        return new[] { type.GetTypeOfT() };
        //    }

        //    Type[] result = null;
        //    List<Type> list = null;
        //    List<PropertyInfo> relations = type.GetProperties().Where(
        //                                        a => (ShouldNormalize(a.PropertyType) && !a.PropertyType.IsEnum) || (a.PropertyType != typeof(string) && a.PropertyType.IsCollection())
        //                                   ).ToList();

        //    if (relations != null && relations.Count > 0)
        //    {
        //        foreach (PropertyInfo prop in relations)
        //        {
        //            Type propType = prop.PropertyType;

        //            if (list == null)
        //            {
        //                list = new List<Type>();
        //            }

        //            list.Add(propType);
        //        }

        //        result = list?.Distinct().ToArray();
        //    }

        //    return result;
        //}

        //private Dictionary<Type, Type[]> GetSubTablesAccessed()
        //{
        //    List<Type> typesToCheck = GetRelationships(_type).Distinct().ToList();
        //    Dictionary<Type, Type[]> result = new Dictionary<Type, Type[]>();
        //    Type[] relations = null;

        //    for (int i = 0; i < typesToCheck.Count; i++)
        //    {
        //        relations = GetRelationships(typesToCheck[i]);

        //        result.Add(typesToCheck[i], relations);

        //        if (relations != null)
        //        {
        //            typesToCheck.AddRange(relations);
        //        }
        //    }

        //    return result;
        //}

        private void LogThenThrow(Exception ex)
        {
            if (ex == null)
            {
                new ArgumentNullException("ex").Message.LogInDebug();
                return;
            }
            else
            {
                ex.Message.LogInDebug();

                _errorLog?.Insert(
                 new Error(ex, JObject.FromObject(
                     new
                     {
                         TableLayer = _tableLayer,
                         LastQuery = _lastQueryExcuted,
                         Type = _type,
                         IdType = IdType,
                         NullLock = _nullLock
                     }).ToString())
                );

                throw ex;
            }
        }

        private void MapCollection(Type collection, ref List<EntityMap> entities, Type parent, string collectionName)
        {
            Func<Type, EntityColumn[]> getColumns = (a) =>
            {
                List<EntityColumn> list = new List<EntityColumn>();
                for (int i = 0; i < 2; i++)
                {
                    list.Add(new EntityColumn(
                          (i == 0) ? "" : collectionName
                        , (i == 0) ? parent.Name + "Id"
                                   : (collection.GetTypeOfT().IsSystemType())
                                   ? "Serialized" + collection.GetTypeOfT().Name + "Collections"
                                   : collection.GetTypeOfT().Name + "Id"
                        , (i == 0) ? true : false
                        , (i == 0) ? true : false
                        , DeterminSQLType((i == 0) ? typeof(int) : (collection.GetTypeOfT().IsSystemType()) ? typeof(string) : typeof(int))
                    ));
                }

                return list.ToArray();
            };

            entities.Add(new EntityMap(
                        collection
                        , new EntityTable(parent.Name + "_" + collectionName + "_" + GetTableName(collection))
                        , getColumns(collection)
                        , new[] { new EntityAssociation(
                             parent
                           , collectionName
                           , parent.Name + "Id"
                           , parent.Name
                           , GetPKOfTable(parent)) }
                        , collectionName + collection.Name));
        }

        private void MapType(Type type, ref List<EntityMap> entities)
        {
            PropertyInfo[] relations = type.GetProperties().Where(a => !a.PropertyType.IsEnum && ShouldNormalize(a.PropertyType)).ToArray(),
                           notMappedProps = GetPropsByAttribute<NotMappedAttribute>(type).ToArray();

            EntityColumn[] getColumns()
            {
                bool needsPK = NeedsIdProp(type, out int ordinal);
                List<EntityColumn> list = new List<EntityColumn>();
                List<PropertyInfo> baseProps = type.GetProperties().ToList();
                PropertyInfo pk = baseProps[ordinal];

                foreach (PropertyInfo prop in baseProps)
                {
                    if (prop.PropertyType.IsCollection() || notMappedProps.Contains(prop))
                        continue;

                    bool isPk = (pk != prop || needsPK) ? false : true;
                    list.Add(new EntityColumn(
                          prop.Name
                        , ShouldNormalize(prop.PropertyType) ? prop.Name + "Id" : prop.Name
                        , isPk ? true : false
                        , isPk ? true : false
                        , DeterminSQLType(prop.PropertyType)
                        , prop
                    ));
                }

                return list.ToArray();
            };

            EntityAssociation[] getAssociations()
            {
                List<EntityAssociation> list = new List<EntityAssociation>();
                PropertyInfo[] props = type.GetProperties().Where(
                                               b => ShouldNormalize(b.PropertyType) && !notMappedProps.Contains(b) //(_ignoredProps.All(a => a.Value.All(c => c != b)))
                                            ).ToArray();

                foreach (PropertyInfo prop in props)
                {
                    list.Add(new EntityAssociation(
                          prop.PropertyType
                        , prop.Name
                        , prop.Name + "Id"
                        , prop.PropertyType.Name
                        , GetPKOfTable(prop.PropertyType)
                    ));
                }

                return list.ToArray();
            };

            entities.Add(new EntityMap(
                          type
                        , new EntityTable(GetTableName(type))
                        , getColumns()
                        , getAssociations()
                        , type.Name.SafeName()));

            if (relations != null)

                foreach (PropertyInfo relation in relations)

                    if (relation.PropertyType.IsCollection())
                        MapCollection(relation.PropertyType, ref entities, type, relation.Name);
                    else
                        MapType(relation.PropertyType, ref entities);
        }

        private bool NeedsIdProp(Type type, out int ordinal)
        {
            ordinal = 0;
            PropertyInfo[] props = type.GetProperties();

            if (type.IsEnum)
                return true;

            if (type.IsSystemType())
                return false;

            if (!type.IsClass)
                return false;

            bool result = true;
            PropertyInfo pk = type.GetPropertiesByAttribute<KeyAttribute>()?.FirstOrDefault() ?? props[0];

            if (pk.Name.ToLower().Contains("id") && (pk.PropertyType == typeof(int) || pk.PropertyType == typeof(Guid) || pk.PropertyType == typeof(string)))
                result = false;

            if (!result)
            {
                foreach (PropertyInfo p in props)
                {
                    if (pk.Name != p.Name || pk.PropertyType != p.PropertyType)
                        ordinal++;
                    else
                        break;
                }
            }

            return result;
        }

        private void SetUp(Type type, ORMOptions options = null)
        {
            if (NeedsIdProp(type, out int pkOrdinal))
                throw new Exception("type's PK is the first public property by default or needs to be targeted via [Key] attribute and is an type of Int32, Guid, or String and contains Id in the name to be managed by DBService...");

            if (!ShouldNormalize(type))
                throw new Exception("type's needs to be a custom class to be managed by DBService...");

            #region Declarations

            IdType = type.GetProperties()[pkOrdinal].PropertyType;
            _type = type;
            _errorLog = options?.ErrorLog ?? null;
            _nullLock = options?.NullLock ?? false;

            //MapAllTypes().Log();
            //QueryProvider = new SqlQueryProvider(Connection, XmlMapping.FromXml(MapAllTypes()), QueryPolicy.Default);

            #endregion Declarations

            SetUpQueryFragments();
            SetUpMappedTypes();

            bool doesExist = CheckIfTableExist(_type),
                 isCurrent = _mappedEntities.All(a => CheckIfTypeIsCurrent(a.Type));

            if (!doesExist)
            {

                CreateTable(_type);
            }
            else if (!isCurrent)
            {
                IEnumerable<EntityMap> tablesToUpdate = _mappedEntities.Where(a => !CheckIfTypeIsCurrent(a.Type));

                foreach (EntityMap tbl in tablesToUpdate)
                    BackupAndDropType(tbl);

                CreateTable(_type);

                foreach (EntityMap tbl in tablesToUpdate)
                    UpdateTableFromBackup(tbl.Type);
            }

            WipeTempTables();

        }

        private void SetUpQueryFragments()
        {
            if (_partialProcs == null)
                _partialProcs = new Dictionary<string, string>();

            _partialProcs.Add("InsertWithNewIDProcedure",
                "CREATE PROC [dbo].[{0}_Insert] {1} As Begin Declare @NewId {2} Insert Into [dbo].{0}({3}){5} Values({4}) Set @NewId = COALESCE(SCOPE_IDENTITY(), @@IDENTITY) {6} Select @NewId End");

            _partialProcs.Add("InsertWithIDProcedure",
                "CREATE PROC [dbo].[{0}_Insert] {1} AS BEGIN IF NOT EXISTS( SELECT * FROM {0} WHERE {0}.{4} = {5}) BEGIN INSERT INTO [dbo].{0}({2}) VALUES({3}) END ELSE BEGIN UPDATE {0} SET {6} END END");

            _partialProcs.Add("UpdateProcedure",
                "CREATE PROC [dbo].[{0}_Update] {1} As Begin {2} End");

            _partialProcs.Add("DeleteProcedure",
                "CREATE PROC [dbo].[{0}_Delete] @{1} {2} As Begin Delete {0} Where {1} = @{1} {3} End");

            _partialProcs.Add("SelectProcedure",
                "CREATE PROC [dbo].[{0}_Select{5}] {3} AS Begin SELECT {1} FROM [dbo].[{0}] {2} {4} End");

            _partialProcs.Add("NullCheckForUpdatePartial",
                "If @{2} Is Not Null Begin Update [dbo].{0} {1} End ");

            _partialProcs.Add("GetPKOfTable",
                "SELECT COLUMN_NAME FROM INFORMATION_SCHEMA.KEY_COLUMN_USAGE WHERE OBJECTPROPERTY(OBJECT_ID(CONSTRAINT_SCHEMA + '.' + QUOTENAME(CONSTRAINT_NAME)), 'IsPrimaryKey') = 1 AND TABLE_NAME = '{0}'");

            _partialProcs.Add("GetAllColumns",
                "SELECT COLUMN_NAME FROM INFORMATION_SCHEMA.COLUMNS WHERE TABLE_NAME = '{0}'");

            _partialProcs.Add("GetAllProcs",
                "SELECT NAME FROM [dbo].[sysobjects] WHERE TYPE = 'P'");

            _partialProcs.Add("CheckIfTableExist",
                "Declare @IsTrue int = 0 IF EXISTS(SELECT * FROM INFORMATION_SCHEMA.TABLES WHERE TABLE_NAME = N'{0}') Begin Set @IsTrue = 1 End Select @IsTrue");

            _partialProcs.Add("CreateTableType",
                "CREATE TYPE [dbo].[{0}] AS TABLE( {1} )");

            _partialProcs.Add("CreateTable",
                "Declare @isTrue int = 0 Begin CREATE TABLE [dbo].[{0}] ( {1} ); IF EXISTS(SELECT* FROM INFORMATION_SCHEMA.TABLES WHERE TABLE_NAME = N'{0}') Begin Set @IsTrue = 1 End End Select @IsTrue");

            _partialProcs.Add("BackupDB", "BACKUP DATABASE {0} TO DISK = '{1}'");

            _partialProcs.Add("CreateColumn", "[{0}] {1} {2}");

            _partialProcs.Add("Select", " SELECT {0}");
            _partialProcs.Add("From", " FROM [dbo].[{0}]");
            _partialProcs.Add("InsertInto", " INSERT INTO [dbo].[{0}]({1})");
            _partialProcs.Add("Update", " UPDATE {0}");
            _partialProcs.Add("Set", " SET {0}");
            _partialProcs.Add("Values", " VALUES({2})");
            _partialProcs.Add("CopyTable", "SELECT {2} INTO {1} FROM {0}");
            _partialProcs.Add("If", " IF {0} BEGIN {1} END");
            _partialProcs.Add("Else", " ELSE BEGIN {0} END");
            _partialProcs.Add("ElseIf", " ELSE IF BEGIN {0} END");
            _partialProcs.Add("Declare", " DECLARE {0} {1} = {2}");
            _partialProcs.Add("DeleteRows", " DELETE {0}");
            _partialProcs.Add("DropTable", " DROP TABLE {0}");
            _partialProcs.Add("DropTableType", " DROP TYPE [dbo].[{0}]");
            _partialProcs.Add("DropProc", " DROP PROCEDURE {0}");
            _partialProcs.Add("Where", " WHERE {0}");
            _partialProcs.Add("BeginEnd", " BEGIN {1} END");
            _partialProcs.Add("Count", " COUNT({0})");
            _partialProcs.Add("GroupBy", " GROUP BY {0}");
            _partialProcs.Add("PK", "PRIMARY KEY CLUSTERED ([{0}] ASC)");
            _partialProcs.Add("IdentityInsert", " SET IDENTITY_INSERT [dbo].[{0}] {1}");

            _procTemplates = new Dictionary<string, string>
                {
                    { "Insert",  _partialProcs["InsertWithNewIDProcedure"]},
                    { "InsertWithID",  _partialProcs["InsertWithIDProcedure"]},
                    { "Update",  _partialProcs["UpdateProcedure"]},
                    { "SelectAll",  _partialProcs["SelectProcedure"]},
                    { "SelectBy",  _partialProcs["SelectProcedure"]},
                    { "Delete",  _partialProcs["DeleteProcedure"]}
                };
        }

        private bool ShouldNormalize(Type type)
        {
            return (type.IsSystemType())
                  ? false
                  : (type.IsCollection())
                  ? false
                  : (type.IsClass || type.IsEnum)
                  ? true
                  : false;
        }

        private void UpdateTableFromBackup(Type type)
        {
            if (type.IsEnum)
                return;

            EntityMap map = (_mappedEntities.Any(a => a.Type == type)) ? _mappedEntities.Single(a => a.Type == type) : null;
            IEnumerable<EntityMap> collectionRelations = _mappedEntities.Any(a => a.Type.IsCollection() && a.Association.Any(b => b.Type == type))
                                                       ? _mappedEntities.Where(a => a.Type.IsCollection() && a.Association.Any(b => b.Type == type))
                                                       : null;

            if (map != null)
                foreach (EntityAssociation tbl in map.Association)
                    UpdateTableFromBackup(tbl.Type);

            UpdateTable(type);

            if (collectionRelations != null && collectionRelations.Count() > 0)
                foreach (EntityMap collection in collectionRelations)
                {
                    if (!collection.Type.GetTypeOfT().IsSystemType())
                        UpdateTableFromBackup(collection.GetTypeOfT());

                    UpdateTable(collection.Type, type.Name + "_");
                }
        }

        private void GetReferredTables(Type type)
        {
            string query = $@"SELECT
                               OBJECT_NAME(f.parent_object_id) TableName,
                               COL_NAME(fc.parent_object_id,fc.parent_column_id) ColName,
                               OBJECT_NAME (f.referenced_object_id) ReferredTableName
                            FROM
                               sys.foreign_keys AS f
                            INNER JOIN
                               sys.foreign_key_columns AS fc
                                  ON f.OBJECT_ID = fc.constraint_object_id
                            INNER JOIN
                               sys.tables t
                                  ON t.OBJECT_ID = fc.referenced_object_id
                            WHERE
                               OBJECT_NAME (f.parent_object_id) = '{GetTableName(type)}'";
        }

        private void WipeDB()
        {
            "Wiping DB Completely... \n".LogInDebug();

            string query = @"
                declare @n char(1)
                set @n = char(10)

                declare @stmt nvarchar(max)

                -- procedures
                select @stmt = isnull( @stmt + @n, '' ) +
                    'drop procedure [' + schema_name(schema_id) + '].[' + name + ']'
                from sys.procedures

                -- check constraints
                select @stmt = isnull( @stmt + @n, '' ) +
                'alter table [' + schema_name(schema_id) + '].[' + object_name( parent_object_id ) + ']    drop constraint [' + name + ']'
                from sys.check_constraints

                -- functions
                select @stmt = isnull( @stmt + @n, '' ) +
                    'drop function [' + schema_name(schema_id) + '].[' + name + ']'
                from sys.objects
                where type in ( 'FN', 'IF', 'TF' )

                -- views
                select @stmt = isnull( @stmt + @n, '' ) +
                    'drop view [' + schema_name(schema_id) + '].[' + name + ']'
                from sys.views

                -- foreign keys
                select @stmt = isnull( @stmt + @n, '' ) +
                    'alter table [' + schema_name(schema_id) + '].[' + object_name( parent_object_id ) + '] drop constraint [' + name + ']'
                from sys.foreign_keys

                -- tables
                select @stmt = isnull( @stmt + @n, '' ) +
                    'drop table [' + schema_name(schema_id) + '].[' + name + ']'
                from sys.tables

                -- user defined types
                select @stmt = isnull( @stmt + @n, '' ) +
                    'drop type [' + schema_name(schema_id) + '].[' + name + ']'
                from sys.types
                where is_user_defined = 1

                exec sp_executesql @stmt";

            Query.ExecuteNonQuery(() => Connection, query, null, null, (mod) => mod.CommandType = CommandType.Text);
        }

        private void WipeTempTables()
        {
            "Wiping DB Completely... \n".LogInDebug();

            string query = "SET QUOTED_IDENTIFIER OFF EXEC sp_msforeachtable \"IF('?' IN(SELECT '[' + TABLE_SCHEMA + '].[' + TABLE_NAME + ']' FROM INFORMATION_SCHEMA.TABLES WHERE TABLE_NAME LIKE '%temp%')) BEGIN DROP TABLE? END \"";

            Query.ExecuteNonQuery(() => Connection, query, null, null, (mod) => mod.CommandType = CommandType.Text);
        }

        #endregion Internal Logic

        #region String Generation

        private string DeterminSQLType(Type type, bool needsDefault = false, bool isPK = false)
        {
            string statement = null;
            type = Nullable.GetUnderlyingType(type) ?? type;

            if (ShouldNormalize(type))
            {
                statement = "INT";
            }
            else
            {
                switch (type.Name)
                {
                    case nameof(JObject):
                        statement = "JSON";
                        break;

                    case nameof(Guid):
                        statement = "UNIQUEIDENTIFIER" + ((needsDefault) ? " DEFAULT(NEWID())" : "");
                        break;

                    case nameof(String):
                        statement = "NVARCHAR (" + ((isPK) ? "128" : "MAX") + ")" + ((needsDefault) ? " DEFAULT(CAST(NEWID() AS NVARCHAR (128)))" : "");
                        break;

                    case nameof(Int16):
                        statement = "SMALLINT";
                        break;

                    case nameof(Int32):
                        statement = "INT";
                        break;

                    case nameof(Int64):
                        statement = "BIGINT";
                        break;

                    case nameof(Decimal):
                        statement = "DECIMAL";
                        break;

                    case nameof(Double):
                        statement = "FLOAT";
                        break;

                    case nameof(Single):
                        statement = "REAL";
                        break;

                    case nameof(TimeSpan):
                        statement = "TIME";
                        break;

                    case nameof(DateTimeOffset):
                        statement = "DATETIMEOFFSET" + ((needsDefault) ? " DEFAULT(CAST(GETDATE() AS DATETIMEOFFSET)" : "");
                        break;

                    case nameof(Boolean):
                        statement = "BIT";
                        break;

                    case nameof(DateTime):
                        statement = "DATETIME2 (7)" + ((needsDefault) ? " DEFAULT(GETDATE())" : "");
                        break;

                    default:
                        statement = "NVARCHAR (" + ((isPK) ? "128" : "MAX") + ")" + ((needsDefault) ? " DEFAULT(CAST(NEWID() AS NVARCHAR (128)))" : "");
                        break;
                }
            }

            return statement;
        }

        private string GetCreateIntermaiateTableQuery(Type parentType, PropertyInfo collection)
        {
            if (!parentType.GetProperties().Any(a => a == collection))
                throw new Exception("parentClass does not have any properties of the collection Type");

            List<string> columns = new List<string>();
            Type collType = collection.PropertyType,
                 listType = collection.PropertyType.GetTypeOfT();

            string parentName = parentType.Name.SafeName(),
                   childName = listType.Name.SafeName();
            NeedsIdProp(parentType, out int ordinal);
            Type parentIdType = parentType.GetPropertyType(ordinal);

            if (ShouldNormalize(listType))
            {
                string PK = CreateTable(listType);
                string FKs = " CONSTRAINT [FK_"
                           + GetTableName(collType, parentType.Name + '_' + collection.Name + '_')
                           + "_" + GetTableName(listType)
                           + "] FOREIGN KEY ([" + listType.Name + "Id]) REFERENCES [dbo].[" + GetTableName(listType) + "] ([" + PK + "])";

                FKs += ", CONSTRAINT [FK_" + GetTableName(parentType) + "_"
                    + GetTableName(collType, parentType.Name + '_' + collection.Name + '_')
                    + "] FOREIGN KEY ([" + parentName + "Id]) REFERENCES [dbo].[" + GetTableName(parentType) + "] ([" + PK + "])";

                for (int i = 0; i < 2; i++)
                {
                    columns.Add(
                        _partialProcs["CreateColumn"].FormatString(
                            i == 0 ? parentName + "Id" : listType.Name + "Id",
                            DeterminSQLType(typeof(int)),
                            "NOT NULL, " + ((i == 0) ? "" : FKs)
                        )
                    );
                }
            }
            else
            {
                for (int i = 0; i < 2; i++)
                {
                    columns.Add(
                        _partialProcs["CreateColumn"].FormatString(
                            i == 0 ? parentName + "Id" : "Serialized" + GetTableName(collType),
                            i == 0 ? DeterminSQLType(parentIdType) : DeterminSQLType(typeof(string)),
                            "NOT NULL" + ((i == 0) ? ", " : "")
                        )
                    );
                }
            }

            string table = string.Concat(columns.ToArray());
            string query = string.Format(_partialProcs["CreateTable"], GetTableName(collType, parentName + '_' + collection.Name + '_'), table);

            return query;
        }

        private string GetCreateTableQuery(Type type)
        {
            string result = null;

            if (type.IsEnum)
                result = GetCreateTableQueryForEnum(type);
            else if (ShouldNormalize(type))
                result = GetCreateTableQueryForClass(type);

            return result;
        }

        private string GetCreateTableQueryForClass(Type type)
        {
            bool needsPK = NeedsIdProp(type, out int pkOrdinal);
            PropertyInfo[] baseProps = type.GetProperties(),
                           notMappedProps = GetPropsByAttribute<NotMappedAttribute>(type).ToArray();
            List<string> columns = new List<string>(),
                         FKs = new List<string>();

            for (int i = 0; i < baseProps.Length; i++)
            {
                string FK = null;

                if (notMappedProps.Contains(baseProps[i]))
                    continue;
                else if (baseProps[i].PropertyType.IsCollection())
                    continue;
                else if (ShouldNormalize(baseProps[i].PropertyType))
                {
                    string normalizedTblPK = CreateTable(baseProps[i].PropertyType);

                    FK = "CONSTRAINT [FK_" + GetTableName(type) + "_" + baseProps[i].Name + "] FOREIGN KEY ([" + baseProps[i].Name + "Id]) REFERENCES [dbo].[" + GetTableName(baseProps[i].PropertyType) + "] ([" + normalizedTblPK + "])";

                    if (FK != null)
                    {
                        FKs.Add(FK);
                    }
                }

                columns.Add(
                        _partialProcs["CreateColumn"].FormatString(

                            !ShouldNormalize(baseProps[i].PropertyType)
                                ? baseProps[i].Name
                                : baseProps[i].Name + "Id",

                            DeterminSQLType(baseProps[i].PropertyType, pkOrdinal == i, pkOrdinal == i),

                            (pkOrdinal == i && baseProps[i].PropertyType == typeof(int))
                                ? "IDENTITY (1, 1) NOT NULL, "
                                : "{0}NULL, ".FormatString(
                                    (pkOrdinal == i || (_nullLock && !baseProps[i].PropertyType.IsNullable())) ? "NOT " : ""
                                )
                        )
                    );
            }

            columns.Add("CONSTRAINT [PK_" + GetTableName(type) + "] PRIMARY KEY CLUSTERED ([" + baseProps[pkOrdinal].Name + "] ASC)," + string.Join(", ", FKs.ToArray()));

            string table = string.Concat(columns.ToArray());
            string query = _partialProcs["CreateTable"].FormatString(GetTableName(type), table);

            return query;
        }

        private string GetCreateTableQueryForEnum(Type type)
        {
            List<string> columns = new List<string>();

            for (int i = 0; i < 3; i++)
            {
                columns.Add(
                    _partialProcs["CreateColumn"].FormatString(
                        i == 0 ? "Id" : i == 1 ? "Name" : "Value",
                        DeterminSQLType(i == 0 ? typeof(int) : i == 1 ? typeof(string) : typeof(int)),
                        (i == 0)
                            ? "IDENTITY (1, 1) NOT NULL, " :
                        (i == 1)
                            ? "NOT NULL, "
                            : "NOT NULL, CONSTRAINT [PK_" + GetTableName(type) + "] PRIMARY KEY CLUSTERED ([Id] ASC)"
                    )
                 );
            }

            string table = string.Concat(columns.ToArray());
            string query = _partialProcs["CreateTable"].FormatString(GetTableName(type), table);

            return query;
        }

        private string GetProcsForClass(Type type, KeyValuePair<string, string> template)
        {
            if (!ShouldNormalize(type))
                throw new Exception("type's Type has to be a custom data type...");

            if (type.IsEnum)
                return GetProcsForEnum(type, template);

            List<int> skippedProps = new List<int>(); ;
            string query = null;
            string inputParams = null,
                   columns = null,
                   values = null,
                   select = null,
                   joins = null;
            List<string> inputs = new List<string>(),
                         colm = new List<string>(),
                         val = new List<string>(),
                         sel = new List<string>(),
                         jns = new List<string>(),
                         innerUpdt = new List<string>();

            PropertyInfo[] props = type.GetProperties();
            bool needsPK = NeedsIdProp(type, out int pkOrdinal);

            for (int i = 0; i < props.Length; i++)
            {
                if (props[i].PropertyType.IsCollection() || GetPropsByAttribute<NotMappedAttribute>(type).Contains(props[i]))
                {
                    skippedProps.Add(i);
                    continue;
                }

                if (i != pkOrdinal)
                {
                    inputs.Add("@" + props[i].Name + " "
                        + DeterminSQLType(props[i].PropertyType, false)
                        + ((props[props.Length - 1] == props[i] || (props[props.Length - 1] == props[i + 1] && props[i + 1].PropertyType.IsCollection()))
                        ? "" : ",")
                    );

                    colm.Add('[' +
                        ((ShouldNormalize(props[i].PropertyType)
                            ? props[i].Name + "Id"
                            : props[i].Name))

                            + ((props[props.Length - 1] == props[i] || (props[props.Length - 1] == props[i + 1] && props[i + 1].PropertyType.IsCollection()))
                                ? "]" : "],")
                    );

                    val.Add(
                        "@" + props[i].Name
                        + ((props[props.Length - 1] == props[i] || (props[props.Length - 1] == props[i + 1] && props[i + 1].PropertyType.IsCollection()))
                        ? "" : ",")
                    );

                    innerUpdt.Add(
                        "SET [" +
                        ((ShouldNormalize(props[i].PropertyType)
                                ? props[i].Name + "Id"
                                : props[i].Name))
                         + "] = @" + props[i].Name
                         + " WHERE " + GetTableName(type) + "."
                         + props[pkOrdinal].Name + " = @" + props[pkOrdinal].Name
                    );
                }
                else
                {
                    skippedProps.Add(i);
                }

                if (ShouldNormalize(props[i].PropertyType))
                {
                    jns.Add(
                        "Inner Join " + GetTableName(props[i].PropertyType)
                        + " AS _" + props[i].Name
                        + " ON _" + props[i].Name + "." +
                        (props[i].PropertyType.IsEnum || needsPK
                            ? "Id"
                            : GetPKOfTable(props[i].PropertyType))
                        + " = " + GetTableName(type) + "."
                        + props[i].Name + "Id"
                    );
                }

                sel.Add(
                    GetTableName(type) + ".[" +
                    ((ShouldNormalize(props[i].PropertyType)
                            ? props[i].Name + "Id"
                            : props[i].Name))
                    + "]"
                    + ((props[props.Length - 1] == props[i] || (props[props.Length - 1] == props[i + 1] && props[i + 1].PropertyType.IsCollection()))
                        ? " "
                        : ",")
                );
            }

            inputParams = string.Join(" ", inputs.ToArray());
            columns = string.Join(" ", colm.ToArray());
            values = string.Join(" ", val.ToArray());
            select = string.Join(" ", sel.ToArray());
            joins = string.Join(" ", jns.ToArray());

            switch (template.Key)
            {
                case "Insert":
                    query = template.Value.FormatString(
                                            GetTableName(type)
                                            , inputParams
                                            , DeterminSQLType(props[pkOrdinal].PropertyType) +
                                                ((props[pkOrdinal].PropertyType != typeof(string)) ? "" : "DECLARE @OUT TABLE (ID NVARCHAR(128)) ")
                                            , columns
                                            , values
                                            , (props[pkOrdinal].PropertyType != typeof(string)) ? "" : "OUTPUT INSERTED.ID INTO @OUT(ID) "
                                            , (props[pkOrdinal].PropertyType != typeof(string)) ? "" : " IF @NewId IS NULL BEGIN SET @NewId = (SELECT TOP (1) ID FROM @OUT) END "
                              );
                    break;

                case "Update":
                    string innerQuery = null;
                    for (int i = 0, x = 0, y = 0; i < props.Length; i++)
                    {
                        x = y + i;
                        if (skippedProps.Count > 0 && skippedProps.Any(a => a == i))
                        {
                            y--;
                            continue;
                        }

                        innerQuery += _partialProcs["NullCheckForUpdatePartial"].FormatString(
                                            GetTableName(type)
                                            , innerUpdt[x]
                                            , props[i].Name);
                    }

                    query = template.Value.FormatString(
                                            GetTableName(type)
                                            , "@{0} {1}, ".FormatString(props[pkOrdinal].Name, DeterminSQLType(props[pkOrdinal].PropertyType)) + inputParams
                                            , innerQuery);
                    break;

                case "SelectAll":
                    query = template.Value.FormatString(
                                            GetTableName(type)
                                            , select
                                            , joins
                                            , ""
                                            , ""
                                            , "All");
                    break;

                case "SelectBy":
                    query = template.Value.FormatString(
                                            GetTableName(type)
                                            , select
                                            , joins
                                            , '@' + props[pkOrdinal].Name + " " + DeterminSQLType(props[pkOrdinal].PropertyType)
                                            , "WHERE " + GetTableName(type) + '.' + props[pkOrdinal].Name + " = @" + props[pkOrdinal].Name
                                            , "ById");
                    break;

                case "Delete":
                    query = template.Value.FormatString(
                                            GetTableName(type)
                                            , props[pkOrdinal].Name
                                            , DeterminSQLType(props[pkOrdinal].PropertyType)
                                            , "");
                    break;
            }

            return query;
        }

        private string GetProcsForCollection(Type type, string prefix, KeyValuePair<string, string> template)
        {
            if (!type.IsCollection())
                throw new Exception("type has to implement IEnumerable...");

            if (prefix == null)
                throw new Exception("prefix cannot be null...");

            Type collType = type.GetTypeOfT();
            string skimmedPrefix = prefix.Split('_')[0],
                   query = null,
                   inputParams = "@{2}Id {1}, @{0}" + ((collType.IsSystemType()) ? "" : "Id") + " {3}",
                   columns = "[{1}Id], [{0}" + ((collType.IsSystemType()) ? "" : "Id") + "] ",
                   values = "@{1}Id, @{0}" + ((collType.IsSystemType()) ? "" : "Id"),
                   select = "{0}.[{2}Id], {0}.[{1}" + ((collType.IsSystemType()) ? "" : "Id") + "]",
                   update = "[{0}" + ((collType.IsSystemType()) ? "" : "Id") + "] = @{0}" + ((collType.IsSystemType()) ? "" : "Id");

            Type parentType = _mappedEntities.First(a => a.Id == skimmedPrefix).Type;
            NeedsIdProp(parentType, out int ordinal);
            Type parentIdType = parentType.GetPropertyType(ordinal);

            inputParams = inputParams.FormatString(
                                ((collType.IsSystemType())
                                    ? "Serialized" + GetTableName(type)
                                    : collType.Name)
                                //, DeterminSQLType(typeof(int))
                                , DeterminSQLType(parentIdType)
                                , skimmedPrefix
                                , ((collType.IsSystemType())
                                    ? DeterminSQLType(typeof(string))
                                    //: DeterminSQLType(typeof(int)))
                                    : DeterminSQLType(parentIdType))
                           );

            update = update.FormatString(
                            ((collType.IsSystemType())
                                ? "Serialized" + GetTableName(type)
                                : collType.Name));

            columns = columns.FormatString(
                            ((collType.IsSystemType())
                                ? "Serialized" + GetTableName(type)
                                : collType.Name)
                            , skimmedPrefix);

            values = values.FormatString(
                            ((collType.IsSystemType())
                                ? "Serialized" + GetTableName(type)
                                : collType.Name)
                            , skimmedPrefix);

            select = select.FormatString(
                            GetTableName(type, prefix)
                            , ((collType.IsSystemType())
                                ? "Serialized" + GetTableName(type)
                                : collType.Name)
                            , skimmedPrefix);

            switch (template.Key)
            {
                case "InsertWithID":
                    query = template.Value.FormatString(
                                            GetTableName(type, prefix)
                                            , inputParams
                                            , columns
                                            , values
                                            , "[" + skimmedPrefix + "Id]"
                                            , "@" + skimmedPrefix + "Id"
                                            , update);
                    break;

                case "SelectAll":
                    query = template.Value.FormatString(GetTableName(type, prefix), select, "", "", "", "All");
                    break;

                case "Delete":
                    query = template.Value.FormatString(GetTableName(type, prefix), skimmedPrefix + "Id", DeterminSQLType(typeof(int)), "");
                    break;
            }

            return query;
        }

        private string GetProcsForEnum(Type type, KeyValuePair<string, string> template)
        {
            if (type.BaseType != typeof(Enum))
                throw new Exception("type's BaseType has to be typeof(Enum)...");

            string query = null,
                   inputParams = null,
                   columns = null,
                   values = null,
                   select = null,
                   tblName = GetTableName(type);

            inputParams = "@Name " + DeterminSQLType(typeof(string)) + ", @Value " + DeterminSQLType(typeof(int));
            columns = "Name, Value";
            values = "@Name, @Value";
            select = tblName + ".[Id], " + tblName + ".[Name], " + tblName + ".[Value]";

            switch (template.Key)
            {
                case "Insert":
                    query = template.Value.FormatString(
                                              tblName
                                            , inputParams
                                            , DeterminSQLType(typeof(int))
                                            , columns
                                            , values
                                            , ""
                                            , ""
                                            , "");
                    break;

                case "Update":
                    string innerQuery = _partialProcs["NullCheckForUpdatePartial"].FormatString(
                                                                      tblName
                                                                    , "SET Value = @Value WHERE " + tblName + ".Id = @Id"
                                                                    , "Value");

                    query = template.Value.FormatString(
                                              tblName
                                            , " @Id INT, " + inputParams
                                            , innerQuery);
                    break;

                case "SelectAll":
                    query = template.Value.FormatString(
                                              tblName
                                            , select
                                            , ""
                                            , ""
                                            , ""
                                            , "All");
                    break;

                case "SelectBy":
                    query = template.Value.FormatString(
                                              tblName
                                            , select
                                            , ""
                                            , "@Id " + DeterminSQLType(typeof(int))
                                            , "Where " + tblName + ".Id = @Id"
                                            , "ById");
                    break;
            }

            return query;
        }

        private string GetTableName(Type type, string prefix = null)
        {
            string result = null;
            if (!type.IsCollection())
            {
                result = type.Name.IsPlural() ? type.Name : type.Name + "s";
            }
            else
            {
                result = type.GetTypeOfT().Name + "Collections";
            }
            result = result.SafeName();

            return (prefix != null) ? prefix + result : result;
        }

        private string GetUpdateTableQuery(Type type, string prefix = null)
        {
            string query = null;

            if (type.IsCollection())
            {
                Type listType = type.GetTypeOfT();

                string prefixed = prefix.Remove(prefix.Length - 1, 1);

                query = _partialProcs["InsertInto"].FormatString(GetTableName(type, prefix), "{0}Id, {1}" + ((listType.IsSystemType()) ? "Serialized" + GetTableName(type) : "Id").FormatString(prefixed, listType.Name));
                query += _partialProcs["Select"].FormatString("{0}Id, {1}" + ((listType.IsSystemType()) ? "Serialized" + GetTableName(type) : "Id").FormatString(prefixed, listType.Name));
                query += _partialProcs["From"].FormatString("temp" + GetTableName(type, prefix));
            }
            else
            {
                Type pkOrdinalType = null;
                bool needsPK = NeedsIdProp(type, out int pkOrdinal);
                List<PropertyInfo> baseProps = type.GetProperties().ToList(),
                                   excludedProps = GetPropsByAttribute<NotMappedAttribute>(type),
                                   includedProps = (excludedProps != null && excludedProps.Count < 0)
                                                        ? baseProps.Where(a => !excludedProps.Contains(a) || a.PropertyType.IsCollection()).ToList()
                                                        : baseProps;

                List<string> oldColumns = GetOldColumns(type);
                List<string> matchingColumns = oldColumns.Where(a => includedProps.Any(b => a == ((ShouldNormalize(b.PropertyType)) ? b.Name + "Id" : b.Name))).ToList();

                if (!needsPK)
                    pkOrdinalType = baseProps.Where((a, b) => b == pkOrdinal).Single().PropertyType;
                else
                {
                    matchingColumns.Add("Id");
                    pkOrdinalType = typeof(int);
                }

                string columns = "[" + string.Join("], [", matchingColumns) + "]";

                query = (pkOrdinalType == typeof(int))
                            ? _partialProcs["IdentityInsert"].FormatString(GetTableName(type), "ON")
                            : "";
                query += _partialProcs["InsertInto"].FormatString(GetTableName(type), columns);
                query += _partialProcs["Select"].FormatString(columns);
                query += _partialProcs["From"].FormatString("temp" + GetTableName(type));
            }

            return query;
        }

        #endregion String Generation

        #region Internal Writes

        private void AddEnumsAsRows(Type type)
        {
            if (type.BaseType != typeof(Enum))
                throw new Exception("type's BaseType has to be a Enum...");

            FieldInfo[] fields = type.GetFields();
            for (int i = 1; i < fields.Length; i++)
            {
                Query.ExecuteNonQuery(() => Connection,
                                "dbo." + GetTableName(type) + "_Insert",
                                (param) =>
                                {
                                    param.Add(new SqlParameter("Name", fields[i].Name));
                                    param.Add(new SqlParameter("Value", (int)fields[i].GetValue(fields[i])));
                                },
                                null);
            }
        }

        private void BackupDB(string path)
        {
            string query = _partialProcs["BackupDB"].FormatString(Connection.Database, path);
            Query.ExecuteNonQuery(() => Connection, query, null, null, (mod) => mod.CommandType = CommandType.Text);
        }

        private void CreateBackupTable(Type type, string prefix = null)
        {
            if (CheckIfTableExist(type, prefix) && !CheckIfBackUpExist(type, prefix))
            {
                "Making {0} Backup Table... \n".FormatString(GetTableName(type)).LogInDebug();

                string query = _partialProcs["CopyTable"].FormatString(GetTableName(type, prefix), "temp" + GetTableName(type, prefix), "*");
                object result = null;

                _lastQueryExcuted = query;

                Query.ExecuteCmd(() => Connection,
                   query,
                    null,
                    (reader, set) =>
                    {
                        result = DataMapper.MapToObject<object>(reader);
                    },
                    null, mod => mod.CommandType = CommandType.Text);
            }
        }

        private void CreateIntermaiateTables(Type type)
        {
            ++_tableLayer;

            if (type.GetProperties().Length > 0 && type.GetProperties().Any(a => a.PropertyType.IsCollection()))
            {
                foreach (PropertyInfo prop in type.GetProperties())
                {
                    if (!prop.PropertyType.IsCollection())
                        continue;

                    if (!CheckIfTableExist(type))
                        throw new Exception("{0} has to be a table in the database to make an intermediate table between the two...".FormatString(type.Name));

                    if (!CheckIfTableExist(prop.PropertyType, type.Name.SafeName() + '_' + prop.Name + '_'))
                    {
                        "Making {0} Intermaiate Table... \n".FormatString(GetTableName(prop.PropertyType, type.Name.SafeName() + '_' + prop.Name + '_')).LogInDebug();
                        int isTrue = 0;
                        string query = GetCreateIntermaiateTableQuery(type, prop);

                        _lastQueryExcuted = query;

                        Query.ExecuteCmd(() => Connection,
                              query,
                               null,
                               (reader, set) =>
                               {
                                   isTrue = reader.GetSafeInt32(0);
                               },
                               null,
                               mod => mod.CommandType = CommandType.Text);

                        if (isTrue != 1)
                            throw new Exception("Intermediate Table Create between {0} and {1} was not successful...".FormatString(type.Name, prop.PropertyType.Name));
                    }

                    CreateProcedures(prop.PropertyType, type.Name.SafeName() + '_' + prop.Name + "_");
                }
            }

            --_tableLayer;
        }

        private void CreateProcedures(Type type, string prefix = null)
        {
            List<string> procs = GetProcs(type, prefix);

            foreach (KeyValuePair<string, string> template in _procTemplates)
            {
                "Making {0} Proc for {1}... \n".FormatString(template.Key, GetTableName(type, prefix)).LogInDebug();
                string nameToCheck = template.Key.Contains("Insert") ? "Insert" : template.Key,
                       query = null;

                if (procs != null && procs.Any(a => a.Contains(nameToCheck)))
                    continue;

                if (type.IsCollection())
                {
                    if (template.Key == "Insert" || template.Key == "Update" || template.Key == "SelectBy")
                        continue;

                    query = GetProcsForCollection(type, prefix, template);
                }
                else if (type.IsEnum)
                {
                    if (template.Key == "Delete" || template.Key == "InsertWithID")
                        continue;

                    query = GetProcsForEnum(type, template);
                }
                else if (ShouldNormalize(type))
                {
                    if (template.Key == "InsertWithID")
                        continue;

                    query = GetProcsForClass(type, template);
                }

                _lastQueryExcuted = query;

                Query.ExecuteCmd(() => Connection,
                   query,
                    null,
                    (reader, set) =>
                    {
                        object id = DataMapper.MapToObject<object>(reader);
                    },
                    null, mod => mod.CommandType = CommandType.Text);
            }
        }

        private string CreateTable(Type type)
        {
            ++_tableLayer;
            _tableCreation = true;
            string result = null;

            if (NeedsIdProp(type, out int pkOrdinal) && !type.IsEnum)
                type = type.AddProperty(typeof(int), "Id");

            if (!CheckIfTypeIsCurrent(type))
            {
                if (!CheckIfTableExist(type))
                {
                    "Making {0} Table... \n".FormatString(GetTableName(type)).LogInDebug();
                    string query = GetCreateTableQuery(type);
                    int isTrue = 0;

                    _lastQueryExcuted = query;

                    Query.ExecuteCmd(() => Connection,
                       query,
                        null,
                        (reader, set) =>
                        {
                            isTrue = reader.GetSafeInt32(0);
                        },
                        null,
                        mod => mod.CommandType = CommandType.Text);

                    if (isTrue != 1)
                        throw new Exception("{0} Table Creation was not successful...".FormatString(type.Name));
                }

                CreateIntermaiateTables(type);
                CreateProcedures(type);

                if (type.IsEnum)
                {
                    AddEnumsAsRows(type);
                    result = "Id";
                }
                else if (ShouldNormalize(type))
                    result = type.GetProperties()[pkOrdinal].Name;
            }
            else
            {
                if (type.IsEnum)
                    result = "Id";
                else if (ShouldNormalize(type))
                    result = type.GetProperties()[pkOrdinal].Name;
            }

            --_tableLayer;
            _tableCreation = (_tableLayer == 0) ? false : true;

            return result;
        }

        private void DropBackupTable(Type type, string prefix = null)
        {
            if (CheckIfBackUpExist(type, prefix))
            {
                string tblName = GetTableName(type, prefix),
                       query = _partialProcs["DropTable"].FormatString("temp" + tblName);
                object result = null;

                _lastQueryExcuted = query;

                Query.ExecuteCmd(() => Connection,
                   query,
                    null,
                    (reader, set) =>
                    {
                        result = DataMapper.MapToObject<object>(reader);
                    },
                    null, mod => mod.CommandType = CommandType.Text);

                "Dropped Backup Table {0}... \n".FormatString(tblName).LogInDebug();
            }
        }

        private void DropProcedures(Type type, string prefix = null)
        {
            List<string> classProcs = GetProcs(type, prefix);

            if (classProcs != null && classProcs.Count > 0)
            {
                foreach (string proc in classProcs)
                {
                    string query = _partialProcs["DropProc"].FormatString(proc);
                    object result = null;

                    _lastQueryExcuted = query;

                    Query.ExecuteCmd(() => Connection,
                       query,
                        null,
                        (reader, set) =>
                        {
                            result = DataMapper.MapToObject<object>(reader);
                        },
                        null, mod => mod.CommandType = CommandType.Text);

                    "Dropped Proc {0}... \n".FormatString(proc).LogInDebug();
                }
            }
        }

        private void DropTable(Type type, string prefix = null)
        {
            if (CheckIfTableExist(type, prefix))
            {
                object result = null;
                string tblName = GetTableName(type, prefix),
                       query = _partialProcs["DropTable"].FormatString(tblName);

                _lastQueryExcuted = query;

                Query.ExecuteCmd(() => Connection,
                   query,
                    null,
                    (reader, set) =>
                    {
                        result = DataMapper.MapToObject<object>(reader);
                    },
                    null, mod => mod.CommandType = CommandType.Text);

                "Dropped Table {0}... \n".FormatString(tblName).LogInDebug();
            }
        }

        private void UpdateTable(Type type, string prefix = null)
        {
            if (CheckIfBackUpExist(type, prefix) && CheckIfTableExist(type, prefix))
            {
                string query = GetUpdateTableQuery(type, prefix);

                "Updating Table {0} From It's Backup Table... \n".FormatString(GetTableName(type)).LogInDebug();
                Query.ExecuteNonQuery(() => Connection, query, null, null, mod => mod.CommandType = CommandType.Text);

                DropBackupTable(type, prefix);
            }
        }

        #endregion Internal Writes

        #region Internal Reads

        private bool CheckIfBackUpExist(Type type, string prefix = null)
        {
            bool result = false;
            string tblName = GetTableName(type, prefix),
                   query = _partialProcs["CheckIfTableExist"].FormatString("temp" + tblName);
            _lastQueryExcuted = query;

            int isTrue = 0;
            Query.ExecuteCmd(() => Connection,
               query,
                null,
                (reader, set) =>
                {
                    isTrue = reader.GetSafeInt32(0);
                },
                null, mod => mod.CommandType = CommandType.Text);

            if (isTrue == 1)
                result = true;
            else
            {
                "{0} Backup Table does not exist... \n".FormatString(tblName).LogInDebug();
                result = false;
            }
            return result;
        }

        private bool CheckIfEnumIsCurrent(Type type)
        {
            bool result = false;
            string tblName = GetTableName(type),
                   query = "SELECT * FROM {0}".FormatString(tblName);
            Dictionary<int, string> currentEnums = type.EnumToDictionary(),
                                    dbEnums = null;
            _lastQueryExcuted = query;

            Query.ExecuteCmd(() => Connection, query, null,
                (reader, set) =>
                {
                    if (dbEnums == null)
                        dbEnums = new Dictionary<int, string>();

                    int key = reader.GetSafeInt32(2);
                    string value = reader.GetSafeString(1);

                    if (!dbEnums.ContainsKey(key))
                        dbEnums.Add(key, value);
                }, null, cmd => cmd.CommandType = CommandType.Text);

            if (dbEnums != null && currentEnums.IsEqualTo(dbEnums))
                result = true;
            else
                "Enum {0} is not current... \n".FormatString(tblName).LogInDebug();

            return result;
        }

        private bool CheckIfTableExist(Type type, string prefix = null)
        {
            bool result = false;
            string tblName = GetTableName(type, prefix),
                   query = _partialProcs["CheckIfTableExist"].FormatString(tblName);
            _lastQueryExcuted = query;

            int isTrue = 0;
            Query.ExecuteCmd(() => Connection,
               query,
                null,
                (reader, set) =>
                {
                    isTrue = reader.GetSafeInt32(0);
                },
                null, mod => mod.CommandType = CommandType.Text);

            if (isTrue == 1)
                result = true;
            else
            {
                "{0} Table does not exist... \n".FormatString(tblName).LogInDebug();
                result = false;
            }

            return result;
        }

        private bool CheckIfTypeIsCurrent(Type type, string prefix = null)
        {
            bool result = true;
            string output = null;

            if (type.IsEnum)
                return CheckIfEnumIsCurrent(type);
            else if (!CheckIfTableExist(type, prefix))
                result = false;
            else if (ShouldNormalize(type))
            {
                #region Declaration

                bool needsId = NeedsIdProp(type, out int pkOrdinal);
                Dictionary<string, Type> columnsInTable = Query.GetSchema(() => Connection, GetTableName(type));
                PropertyInfo[] baseProps = type.GetProperties(),
                               excludedProps = GetPropsByAttribute<NotMappedAttribute>(type).ToArray(),
                               includedProps = baseProps.Where(a => (excludedProps != null && !excludedProps.Contains(a)) && !a.PropertyType.IsCollection()).ToArray();

                #endregion Declaration

                #region Column Checks

                foreach (KeyValuePair<string, Type> col in columnsInTable)
                {
                    if (needsId && col.Key == "Id")
                        continue;

                    if (!includedProps.Any(
                        (a) =>
                        {
                            bool r = columnsInTable.Any(b => b.Key == (ShouldNormalize(a.PropertyType) ? a.Name + "Id" : a.Name));
                            if ((ShouldNormalize(a.PropertyType) ? a.Name + "Id" : a.Name) == col.Key)
                                r = (Nullable.GetUnderlyingType(a.PropertyType) ?? (ShouldNormalize(a.PropertyType) ? typeof(int) : a.PropertyType)) == col.Value;

                            return r;
                        }))
                    {
                        output = "{0} does not match DB Schema.... Not Current... \n".FormatString(GetTableName(type, prefix));
                        result = false;
                    }
                }

                foreach (PropertyInfo prop in includedProps)
                {
                    if (!columnsInTable.Any(
                            (a) =>
                            {
                                bool r = includedProps.Any(b => a.Key == (ShouldNormalize(b.PropertyType) ? b.Name + "Id" : b.Name)); ;
                                if ((ShouldNormalize(prop.PropertyType) ? prop.Name + "Id" : prop.Name) == a.Key)
                                    r = (Nullable.GetUnderlyingType(prop.PropertyType) ?? (ShouldNormalize(prop.PropertyType) ? typeof(int) : prop.PropertyType)) == a.Value;

                                return r;
                            }))
                    {
                        output = "{0} does not match DB Schema.... Not Current... \n".FormatString(GetTableName(type, prefix));
                        result = false;
                    }
                }

                #endregion Column Checks

                #region Recursive Type Check

                if (includedProps.Any(a => ShouldNormalize(a.PropertyType)))
                {
                    PropertyInfo[] propsToCheck = Basic.DistinctBy(includedProps.Where(a => ShouldNormalize(a.PropertyType)), a => a.PropertyType).ToArray();
                    foreach (PropertyInfo propToCheck in propsToCheck)
                    {
                        if (!CheckIfTypeIsCurrent(propToCheck.PropertyType))
                        {
                            "{0} Is Not Current, Therefore {1} Is Not Current... \n".FormatString(GetTableName(propToCheck.PropertyType), GetTableName(type, prefix)).LogInDebug();
                            result = false;
                        }
                    }
                }

                #endregion Recursive Type Check

                #region Collection Checks

                if (baseProps.Any(a => (excludedProps != null && !excludedProps.Contains(a) && a.PropertyType.IsCollection()) || a.PropertyType.IsCollection()))
                {
                    PropertyInfo[] propsToCheck = baseProps.Where(a => (excludedProps != null && !excludedProps.Contains(a) && a.PropertyType.IsCollection()) || a.PropertyType.IsCollection()).Distinct().ToArray();
                    foreach (PropertyInfo propToCheck in propsToCheck)
                    {
                        Type listType = propToCheck.PropertyType.GetTypeOfT();

                        if (!listType.IsSystemType() && !CheckIfTypeIsCurrent(listType))
                        {
                            output = "{0} Inside Collection Is Not Current... \n".FormatString(GetTableName(listType));
                            result = false;
                        }

                        if (!CheckIfTypeIsCurrent(propToCheck.PropertyType, type.Name.SafeName() + "_" + propToCheck.Name + "_"))
                        {
                            result = false;
                        }
                    }
                }

                #endregion Collection Checks
            }

            #region Proc Checks

            List<string> procs = GetProcs(type, prefix) ?? new List<string>();
            if (type.IsCollection() && procs.Count != 3)
            {
                output = "{0} Does Not Have All Its Procs... Not Current... \n".FormatString(GetTableName(type, prefix));
                result = false;
            }
            else if (type.IsEnum && procs.Count != 4)
            {
                output = "{0} Does Not Have All Its Procs... Not Current... \n".FormatString(GetTableName(type, prefix));
                result = false;
            }
            else if (!type.IsEnum && ShouldNormalize(type) && procs.Count != 5)
            {
                output = "{0} Does Not Have All Its Procs... Not Current... \n".FormatString(GetTableName(type, prefix));
                result = false;
            }

            #endregion Proc Checks

            if (output != null)
                output.LogInDebug();

            return result;
        }

        private List<string> GetOldColumns(Type type)
        {
            string query = _partialProcs["GetAllColumns"].FormatString("temp" + GetTableName(type));
            List<string> list = null;

            _lastQueryExcuted = query;

            Query.ExecuteCmd(() => Connection,
               query,
                null,
                (reader, set) =>
                {
                    string column = DataMapper.MapToObject<string>(reader);
                    if (list == null) { list = new List<string>(); }
                    list.Add(column);
                },
                null, mod => mod.CommandType = CommandType.Text);

            return list;
        }

        private string GetPKOfTable(Type type, string prefix = null)
        {
            bool needsPK = NeedsIdProp(type, out int pkOrdinal);

            if (type.IsEnum || needsPK)
                return "Id";

            string result = null;
            if (CheckIfTableExist(type))
            {
                string query = _partialProcs["GetPKOfTable"].FormatString(GetTableName(type));

                _lastQueryExcuted = query;

                Query.ExecuteCmd(() => Connection,
                   query,
                    null,
                    (reader, set) =>
                    {
                        result = reader.GetString(0);
                    },
                    null, mod => mod.CommandType = CommandType.Text);
            }
            else if (type.IsCollection())
            {
                return prefix + "Id";
            }
            else
            {
                result = type.GetProperties().ElementAt(pkOrdinal).Name;
            }
            return result;
        }

        private List<string> GetProcs(Type type, string prefix = null)
        {
            string query = _partialProcs["GetAllProcs"];
            List<string> list = null;
            _lastQueryExcuted = query;

            Query.ExecuteCmd(() => Connection,
               query,
                null,
                (reader, set) =>
                {
                    string proc = DataMapper.MapToObject<string>(reader);
                    if (list == null) { list = new List<string>(); }
                    list.Add(proc);
                },
                null, mod => mod.CommandType = CommandType.Text);

            List<string> result = list?.Where(
                a =>
                {
                    string[] procSufixs = new[] {
                        "_Select",
                        "_SelectAll",
                        "_SelectById",
                        "_Insert",
                        "_Update",
                        "_Delete"
                    };
                    return procSufixs.Any(b => a == GetTableName(type, prefix) + b);
                }
            ).ToList();

            return result;
        }

        #endregion Internal Reads

        #region Private Access Methods

        private void Delete(Type type, object id)
        {
            object result = type.Instantiate();
            PropertyInfo[] baseProps = type.GetProperties();
            object tableObj = GetNormalizedSchema(type);
            Type tableType = tableObj.GetType();
            bool needsId = NeedsIdProp(type, out int pkOrdinal);

            _lastQueryExcuted = "dbo." + GetTableName(type) + "_SelectById";

            Query.ExecuteCmd(() => Connection, "dbo." + GetTableName(type) + "_SelectById",
                param => param.Add(new SqlParameter((!type.IsEnum && !needsId) ? type.GetProperties()[pkOrdinal].Name : "Id", id)),
                (reader, set) =>
                {
                    tableObj = DataMapper.MapToObject(reader, tableType);
                });

            foreach (PropertyInfo arr in baseProps.Where(a => a.PropertyType.IsCollection() /*&& !a.PropertyType.GetTypeOfT().IsSystemType()*/))
            {
                DeleteCollection((int)id, type, arr);
            }

            _lastQueryExcuted = "dbo." + GetTableName(type) + "_Delete";

            Query.ExecuteNonQuery(() => Connection, "dbo." + GetTableName(type) + "_Delete",
               param => param.Add(new SqlParameter((needsId) ? "Id" : type.GetProperties()[pkOrdinal].Name, id)));

            foreach (PropertyInfo prop in baseProps.Where(a => ShouldNormalize(a.PropertyType) && !a.PropertyType.IsEnum))
            {
                Delete(prop.PropertyType, tableObj.GetPropertyValue(prop.Name + "Id"));
            }
        }

        private void DeleteCollection(int parentId, Type parentType, PropertyInfo property)
        {
            object result = null;
            int[] objIds = null;
            Type propType = property.GetTypeOfT();
            string childTypeName = propType.Name.SafeName(),
                   parentName = parentType.Name.SafeName();

            if (!propType.IsSystemType())
            {
                objIds = GetCollectionIds(parentId, parentType, propType);
            }

            string query = _partialProcs["DeleteRows"].FormatString(parentName = '_' + property.Name + '_' + childTypeName + "Collections")
                         + _partialProcs["Where"].FormatString(parentName + "Id = " + parentId);

            _lastQueryExcuted = query;

            Query.ExecuteCmd(() => Connection, query,
                       null,
                       (reader, set) =>
                       {
                           result = reader.GetSafeInt32(0);
                       }, null, cmd => cmd.CommandType = CommandType.Text);

            if (!propType.IsSystemType())
            {
                DeleteMultiple(propType, objIds?.ToArray());
            }
        }

        private void DeleteMultiple(Type type, int[] ids)
        {
            if (ids == null && ids.Length == 0)
            {
                return;
            }

            bool needsPK = NeedsIdProp(type, out int pkOrdinal);
            object result = null;
            List<object> tableObjs = null;
            Type tableType = GetNormalizedSchema(type).GetType();
            PropertyInfo[] baseProps = type.GetProperties();

            string query = _partialProcs["Select"].FormatString("*")
                            + _partialProcs["From"].FormatString(GetTableName(type))
                            + _partialProcs["Where"].FormatString(GetPKOfTable(type)
                            + " IN (" + String.Join(", ", ids) + ") ");

            _lastQueryExcuted = query;

            Query.ExecuteCmd(() => Connection, query, null,
                (reader, set) =>
                {
                    object tableObj = tableType.Instantiate();
                    tableObj = DataMapper.MapToObject(reader, tableType);

                    if (tableObjs == null)
                    {
                        tableObjs = new List<object>();
                    }

                    tableObjs.Add(tableObj);
                }, null, cmd => cmd.CommandType = CommandType.Text);

            foreach (object item in tableObjs)
            {
                foreach (PropertyInfo arr in baseProps.Where(a => a.PropertyType.IsCollection() /*&& !a.PropertyType.GetTypeOfT().IsSystemType()*/))
                {
                    Type listType = arr.PropertyType.GetTypeOfT();
                    DeleteCollection(
                        (int)item.GetPropertyValue(
                            needsPK ? "Id" : type.GetProperties()[pkOrdinal].Name
                        )
                        , type
                        , arr
                    );
                }
            }

            query = _partialProcs["DeleteRows"].FormatString(GetTableName(type))
                    + _partialProcs["Where"].FormatString(GetPKOfTable(type)
                    + " IN (" + String.Join(", ", ids) + ") ");

            _lastQueryExcuted = query;

            Query.ExecuteCmd(() => Connection, query,
                       null,
                       (reader, set) =>
                       {
                           result = reader.GetSafeInt32(0);
                       }, null, cmd => cmd.CommandType = CommandType.Text);

            foreach (object item in tableObjs)
            {
                foreach (PropertyInfo prop in baseProps.Where(a => ShouldNormalize(a.PropertyType) && !a.PropertyType.IsEnum))
                {
                    Delete(prop.PropertyType, item.GetPropertyValue(prop.Name + "Id"));
                }
            }
        }

        private void DeleteRelationship(Type parent, Type child, object parentId, int childId)
        {
            Type listType = parent.GetProperties().FirstOrDefault(a => a.PropertyType.IsCollection() && a.PropertyType.GetTypeOfT() == child).PropertyType;

            string collectionTbl = parent.Name + "_" + child.Name + "Collections",
                   query = _partialProcs["DeleteRows"].FormatString(collectionTbl)
                         + _partialProcs["Where"].FormatString("{0}Id = {2} AND {1}Id = {3}".FormatString(parent.Name, child.Name, parentId.ToString(), childId.ToString()));

            _lastQueryExcuted = query;

            Query.ExecuteNonQuery(() => Connection, query,
                   null, null, cmd => cmd.CommandType = CommandType.Text, null);

            Delete(child, childId);
        }

        private object Get(Type type, object id)
        {
            object result = null;
            object tableObj = GetNormalizedSchema(type);
            Type tableType = tableObj.GetType();
            bool needsId = NeedsIdProp(type, out int pkOrdinal);
            string pkName = (!type.IsEnum && !needsId) ? type.GetProperties()[pkOrdinal].Name : "Id";

            _lastQueryExcuted = "dbo." + GetTableName(type) + "_SelectById";

            Query.ExecuteCmd(() => Connection, "dbo." + GetTableName(type) + "_SelectById",
                param => param.Add(new SqlParameter(pkName, id)),
                (reader, set) =>
                {
                    tableObj = DataMapper.MapToObject(reader, tableType);
                });

            if (tableObj.GetPropertyValue(pkName) != null ||
               (tableObj.GetPropertyValue(pkName).IsNumeric() && (int)tableObj.GetPropertyValue(pkName) != 0))
            {
                result = InstantateFromTable(type, tableObj);
            }

            return result;
        }

        private List<object> GetAll(Type type, ref Dictionary<KeyValuePair<string, Type>, List<object>> tblEntities, string prefix = null)
        {
            if (tblEntities == null)
            {
                tblEntities = new Dictionary<KeyValuePair<string, Type>, List<object>>();
            }

            List<object> entities = null;
            Type tableType = GetNormalizedSchema(type, prefix).GetType();
            Dictionary<KeyValuePair<string, Type>, List<object>> tableObjs = tblEntities;
            KeyValuePair<string, Type> key = new KeyValuePair<string, Type>(GetTableName(type, prefix), type);

            _lastQueryExcuted = "dbo." + key.Key + "_SelectAll";
            Query.ExecuteCmd(() => Connection, "dbo." + key.Key + "_SelectAll",
                null,
                (reader, set) =>
                {
                    object tableObj = tableType.Instantiate();
                    tableObj = DataMapper.MapToObject(reader, tableType);

                    if (!tableObjs.Any(a => a.Key.Equals(key)))
                    {
                        tableObjs.Add(key, new List<object>());
                    }

                    tableObjs[key].Add(tableObj);
                });

            if (!type.IsCollection())
            {
                foreach (PropertyInfo prop in type.GetProperties())
                {
                    if (ShouldNormalize(prop.PropertyType) && !prop.PropertyType.IsEnum)
                    {
                        GetAll(prop.PropertyType, ref tblEntities);
                    }
                    else if (prop.PropertyType.IsCollection())
                    {
                        GetAll(prop.PropertyType, ref tblEntities, type.Name.SafeName() + '_' + prop.Name.SafeName() + '_');
                        if (!prop.PropertyType.GetTypeOfT().IsSystemType())
                        {
                            GetAll(prop.PropertyType.GetTypeOfT(), ref tblEntities);
                        }
                    }
                }

                if (tblEntities.Any(a => a.Key.Equals(key)))
                {
                    foreach (object tbl in tblEntities[key])
                    {
                        if (entities == null)
                        {
                            entities = new List<object>();
                        }

                        object entity = InstantateFromIds(key, tbl, tblEntities);

                        entities.Add(entity);
                    }
                }
            }

            return entities;
        }

        private int[] GetCollectionIds(object parentId, Type parentType, Type childType)
        {
            if (childType.IsSystemType())
            {
                return null;
            }

            List<int> ids = new List<int>();
            string childName = childType.Name.SafeName(),
                   parentName = parentType.Name.SafeName();

            string query = _partialProcs["Select"].FormatString(childName + "Id")
                         + _partialProcs["From"].FormatString(parentName + "_" + childName + "Collections")
                         + _partialProcs["Where"].FormatString(parentName + "Id = " + parentId);

            _lastQueryExcuted = query;

            Query.ExecuteCmd(() => Connection, query,
                null,
                (reader, set) =>
                {
                    int id = reader.GetSafeInt32(0);
                    ids.Add(id);
                }, null, cmd => cmd.CommandType = CommandType.Text);

            return ids?.ToArray();
        }

        private List<object> GetMultiple(Type type, int[] ids)
        {
            List<object> entities = null;
            if (ids != null && ids.Length > 0)
            {
                List<object> tableObjs = null;
                Type tableType = GetNormalizedSchema(type).GetType();
                string query = _partialProcs["Select"].FormatString("*")
                                    + _partialProcs["From"].FormatString(GetTableName(type))
                                    + _partialProcs["Where"].FormatString(GetPKOfTable(type)
                                    + " IN (" + String.Join(", ", ids) + ") ");

                _lastQueryExcuted = query;

                Query.ExecuteCmd(() => Connection, query, null,
                    (reader, set) =>
                    {
                        object tableObj = tableType.Instantiate();
                        tableObj = DataMapper.MapToObject(reader, tableType);

                        if (tableObjs == null)
                        {
                            tableObjs = new List<object>();
                        }

                        tableObjs.Add(tableObj);
                    }, null, cmd => cmd.CommandType = CommandType.Text);

                foreach (object obj in tableObjs)
                {
                    object entity = InstantateFromTable(type, obj);
                    entities.Add(entity);
                }
            }

            return entities;
        }

        private string GetSerializedCollection(object parentId, Type parentType, PropertyInfo property)
        {
            string result = null;
            string parentTypeName = parentType.Name.SafeName(),
                   childTypeName = property.PropertyType.GetTypeOfT().Name.SafeName();

            string collectionTbl = parentTypeName + '_' + property.Name + '_' + childTypeName + "Collections";
            Type parentIdType = parentId.GetType();
            Type listType = parentType.GetProperties().FirstOrDefault(a => a.PropertyType.IsCollection() && a == property).PropertyType;

            string query = _partialProcs["Select"].FormatString("Serialized" + childTypeName + "Collections")
                         + _partialProcs["From"].FormatString(collectionTbl)
                         + _partialProcs["Where"].FormatString(
                            ((parentIdType == typeof(string)) ? "CAST(" + parentTypeName + "Id AS VARCHAR(MAX)) = " : parentTypeName + "Id = ")
                            + ((parentIdType == typeof(string)) ? "'" + parentId + "'" : parentId)
                         );

            _lastQueryExcuted = query;

            Query.ExecuteCmd(
                        () => Connection
                       , query
                       , null
                       , (reader, set) =>
                       {
                           result = reader.GetSafeString(0);
                       }
                       , null
                       , cmd => cmd.CommandType = CommandType.Text);

            return result;
        }

        private object Insert(object model, Type type, ref Dictionary<KeyValuePair<Type, PropertyInfo>, KeyValuePair<object, object[]>> relations)
        {
            if (model == null)
                model = type.Instantiate();

            object id = null;
            Dictionary<Type, object> refferedIds = new Dictionary<Type, object>();
            PropertyInfo[] normalizedProps = type.GetProperties().Where(a =>
                                                             ((!a.PropertyType.IsEnum && ShouldNormalize(a.PropertyType)) || a.PropertyType.IsCollection()))
                                                             .ToArray();
            if (normalizedProps.Length > 0)
            {
                foreach (PropertyInfo prop in normalizedProps)
                {
                    if (prop.PropertyType.IsCollection())
                    {
                        Type typeInList = prop.PropertyType.GetTypeOfT();
                        if (!typeInList.IsSystemType())
                        {
                            object[] arr = (model.GetPropertyValue(prop.Name) == null) ? null : ((IEnumerable<object>)model.GetPropertyValue(prop.Name)).ToArray();
                            if (arr != null && arr.Length > 0)
                            {
                                List<object> ids = new List<object>();

                                foreach (object item in arr)
                                {
                                    object subId = Insert(item, typeInList, ref relations);
                                    ids.Add(subId);
                                }

                                relations.Add(new KeyValuePair<Type, PropertyInfo>(type, prop), new KeyValuePair<object, object[]>(0, ids.ToArray()));
                            }
                        }
                        else
                        {
                            relations.Add(new KeyValuePair<Type, PropertyInfo>(type, prop), new KeyValuePair<object, object[]>(0, new[] { JsonConvert.SerializeObject(model.GetPropertyValue(prop.Name)) }));
                        }
                    }
                    else if (ShouldNormalize(prop.PropertyType) && !prop.PropertyType.IsEnum)
                    {
                        object subId = Insert(model.GetPropertyValue(prop.Name), prop.PropertyType, ref relations);
                        relations.Add(new KeyValuePair<Type, PropertyInfo>(type, prop), new KeyValuePair<object, object[]>(0, new[] { subId }));
                    }
                }
            }

            foreach (PropertyInfo prop in type.GetProperties())
            {
                if (relations.Any(a => a.Key.Key == type && a.Key.Value == prop))
                {
                    object[] vals = relations.FirstOrDefault(a => a.Key.Key == type && a.Key.Value == prop).Value.Value;
                    if (vals.Length == 1 && vals[0].GetType() != typeof(string))
                    {
                        refferedIds.Add(prop.PropertyType, vals[0]);
                    }
                }
            }

            id = Insert(model, type, refferedIds);

            for (int i = 0; i < relations.Count; i++)
            {
                var relation = relations.ElementAt(i);
                if (relation.Key.Key == type)
                {
                    relations[relation.Key] = new KeyValuePair<object, object[]>(id, relation.Value.Value);

                    if (relation.Value.Value.Length > 1)
                    {
                        foreach (object val in relation.Value.Value)
                        {
                            InsertRelationship(relation.Key.Key, relation.Key.Value.GetTypeOfT(), (int)id, (int)val);
                        }
                    }
                    else if (relation.Value.Value[0].GetType() == typeof(string))
                    {
                        InsertSerializedCollection(relation.Key.Key, relation.Key.Value, id.Cast(id.GetType()), (string)relation.Value.Value[0]);
                    }
                }
            }

            return id;
        }

        private object Insert(object model, Type type, Dictionary<Type, object> ids = null)
        {
            if (ids != null && ids.Values.Any(a => a.GetType().IsCollection()))
                throw new Exception("ids.Values cannot be a collection...");

            if (model.GetType() != type)
                throw new Exception("model Parameter is the wrong type...");

            object id = 0;
            bool needsId = NeedsIdProp(type, out int pkOrdinal);

            _lastQueryExcuted = "dbo." + GetTableName(type) + "_Insert";

            Query.ExecuteCmd(() => Connection, "dbo." + GetTableName(type) + "_Insert",
                       param =>
                       {
                           IEnumerable<PropertyInfo> propsToExclude = type.GetPropertiesByNotMappedAttribute();
                           PropertyInfo[] props = type.GetProperties();

                           foreach (PropertyInfo prop in props)
                           {
                               if (propsToExclude != null && propsToExclude.Any(a => a == prop))
                                   continue;
                               else if (!needsId && prop == props[pkOrdinal])
                                   continue;
                               else if (prop.PropertyType.IsCollection())
                                   continue;
                               else if (prop.PropertyType.IsEnum)
                               {
                                   if (prop.GetValue(model) != null)
                                   {
                                       int enumId = prop.PropertyType.EnumToDictionary().Index(a => a.Key == (int)prop.GetValue(model));
                                       param.Add(new SqlParameter(prop.Name, enumId));
                                   }
                                   else
                                       throw new Exception("Any property in model that is an Enum cannot be null");
                               }
                               else if (ShouldNormalize(prop.PropertyType) && ids.Keys.Any(a => a == prop.PropertyType))
                                   param.Add(new SqlParameter(prop.Name, ids[prop.PropertyType]));
                               else
                               {
                                   object value = null;

                                   if (prop.GetValue(model) != null)
                                       value = prop.GetValue(model);
                                   else
                                       value = DBNull.Value;

                                   param.Add(new SqlParameter(prop.Name, value));
                               }
                           }
                       },
                      (reader, set) =>
                      {
                          id = DataMapper.MapToObject<object>(reader);
                      });

            return id;
        }

        private void InsertRelationship(Type parent, Type child, object parentId, int childId)
        {
            string collectionTbl = parent.Name + "_" + child.Name + "Collections";
            Type listType = parent.GetProperties().FirstOrDefault(a => a.PropertyType.IsCollection() && a.PropertyType.GetTypeOfT() == child).PropertyType;

            _lastQueryExcuted = "dbo." + collectionTbl + "_Insert";

            Query.ExecuteNonQuery(() => Connection, "dbo." + collectionTbl + "_Insert",
                   param =>
                   {
                       for (int i = 0; i < 2; i++)
                       {
                           if (i == 0)
                           {
                               param.Add(new SqlParameter(parent.Name + "Id", parentId));
                           }
                           else
                           {
                               param.Add(new SqlParameter(child.Name + "Id", childId));
                           }
                       }
                   }, null, null, null);
        }

        private void InsertSerializedCollection(Type parentType, PropertyInfo property, object parentId, string serializedCollection)
        {
            if (GetSerializedCollection(parentId, parentType, property) != null)
            {
                UpdateSerializedCollection(parentType, property, parentId, serializedCollection);
            }
            else
            {
                string parentTypeName = parentType.Name.SafeName(),
                       childTypeName = property.PropertyType.GetTypeOfT().Name.SafeName(),
                       collectionTbl = parentTypeName + '_' + property.Name + '_' + childTypeName + "Collections";

                _lastQueryExcuted = "dbo." + collectionTbl + "_Insert";

                Query.ExecuteNonQuery(() => Connection, "dbo." + collectionTbl + "_Insert",
                       param =>
                       {
                           for (int i = 0; i < 2; i++)
                           {
                               if (i == 0)
                               {
                                   param.Add(new SqlParameter(parentTypeName + "Id", parentId));
                               }
                               else
                               {
                                   param.Add(new SqlParameter("Serialized" + childTypeName + "Collections", serializedCollection));
                               }
                           }
                       }, null, null, null);
            }
        }

        private object InstantateFromIds(KeyValuePair<string, Type> pair, object tblOfType, Dictionary<KeyValuePair<string, Type>, List<object>> tblEntities)
        {
            Type type = pair.Value;
            object entity = type.Instantiate();
            string typeName = type.Name.SafeName();

            if (!type.IsCollection())
            {
                foreach (PropertyInfo prop in type.GetProperties())
                {
                    bool needsPK = NeedsIdProp(prop.PropertyType, out int pkOrdinal);
                    KeyValuePair<string, Type> propPair =
                        new KeyValuePair<string, Type>(
                            GetTableName(prop.PropertyType,
                                        (ShouldNormalize(prop.PropertyType) && !prop.PropertyType.IsEnum) ? null : typeName + '_' + prop.Name + '_'
                            ), prop.PropertyType
                        );

                    if (ShouldNormalize(prop.PropertyType) && !prop.PropertyType.IsEnum)
                    {
                        object rowOfProp = tblEntities[propPair]
                                             .FirstOrDefault(
                                                a => a.GetPropertyValue(
                                                        needsPK
                                                            ? "Id"
                                                            : prop.PropertyType.GetProperties()[pkOrdinal].Name
                                                        )
                                                      .Equals(tblOfType.GetPropertyValue(prop.Name + "Id"))
                                             );

                        object property = InstantateFromIds(propPair, rowOfProp, tblEntities);

                        entity.SetPropertyValue(prop.Name, property);
                    }
                    else if (prop.PropertyType.IsCollection())
                    {
                        Type listType = prop.PropertyType.GetTypeOfT();
                        if (!listType.IsSystemType())
                        {
                            List<object> collection = null;
                            KeyValuePair<string, Type> childPair = new KeyValuePair<string, Type>(GetTableName(listType), prop.PropertyType);

                            if (tblEntities.Any(a => a.Key.Equals(propPair)))
                            {
                                object[] relations = tblEntities[propPair]
                                                                    .Where(a => a.GetPropertyValue(typeName + "Id")
                                                                    .Equals(tblOfType.GetPropertyValue(
                                                                        needsPK
                                                                            ? "Id"
                                                                            : prop.PropertyType.GetProperties()[pkOrdinal].Name)
                                                                    )).ToArray();

                                List<object> rowsOfList = tblEntities[childPair].Where(a =>
                                                            relations.Any(b => b.GetPropertyValue(listType.Name + "Id")
                                                            .Equals(a.GetPropertyValue(
                                                                needsPK
                                                                    ? "Id"
                                                                    : listType.GetProperties()[pkOrdinal].Name)
                                                            ))).ToList();

                                foreach (object item in rowsOfList)
                                {
                                    if (collection == null)
                                    {
                                        collection = new List<object>();
                                    }

                                    object obj = InstantateFromIds(childPair, item, tblEntities);

                                    collection.Add(obj);
                                }
                            }

                            entity.SetPropertyValue(prop.Name, collection.Cast(listType));
                        }
                        else
                        {
                            IEnumerable deserializedObj = null;
                            List<object> relations = (!tblEntities.Keys.Contains(propPair)) ? null : tblEntities[propPair];

                            if (relations != null)
                            {
                                string serializedObj = (string)relations[0].GetPropertyValue("Serialized" + GetTableName(prop.PropertyType));
                                deserializedObj = (IEnumerable)JsonConvert.DeserializeObject(serializedObj, prop.PropertyType);
                            }

                            entity.SetPropertyValue(prop.Name, deserializedObj?.Cast(prop.PropertyType.GetTypeOfT()));
                        }
                    }
                    else
                    {
                        object property = tblOfType.GetPropertyValue((prop.PropertyType.IsEnum) ? prop.Name + "Id" : prop.Name);
                        entity.SetPropertyValue(prop.Name, property);
                    }
                }
            }

            return entity;
        }

        private object InstantateFromTable(Type type, object tblOfType)
        {
            object result = type.Instantiate();

            if (type.IsEnum)
                result = tblOfType.GetPropertyValue("Value");
            else
            {
                foreach (PropertyInfo prop in type.GetProperties())
                {
                    if (ShouldNormalize(prop.PropertyType) /*&& !prop.PropertyType.IsEnum*/)
                    {
                        object property = Get(prop.PropertyType, tblOfType.GetPropertyValue(prop.Name + "Id"));
                        result.SetPropertyValue(prop.Name, property);
                    }
                    else if (prop.PropertyType.IsCollection())
                    {
                        Type listType = prop.PropertyType.GetTypeOfT();

                        if (!listType.IsSystemType())
                        {
                            int[] collectionIds = GetCollectionIds(tblOfType.GetPropertyValue(prop.Name + "Id"), type, listType);
                            List<object> collection = GetMultiple(listType, collectionIds);
                            result.SetPropertyValue(prop.Name, collection);
                        }
                        else
                        {
                            string serializedObj = GetSerializedCollection(tblOfType.GetPropertyValue(GetPKOfTable(type)), type, prop);
                            result.SetPropertyValue(prop.Name, JsonConvert.DeserializeObject(serializedObj, prop.PropertyType));
                        }
                    }
                    else
                    {
                        object property = tblOfType.GetPropertyValue(prop.Name /*+ (prop.PropertyType.IsEnum ? "Id" : "")*/);
                        result.SetPropertyValue(prop.Name, property);
                    }
                }
            }

            return result;
        }

        private void Update(object model, object id, Type type)
        {
            if (model == null)
                model = type.Instantiate();

            bool needsId = NeedsIdProp(type, out int pkOrdinal);
            object result = type.Instantiate();
            object tableObj = GetNormalizedSchema(type);
            Type tableType = tableObj.GetType();

            _lastQueryExcuted = "dbo." + GetTableName(type) + "_SelectById";

            Query.ExecuteCmd(() => Connection, "dbo." + GetTableName(type) + "_SelectById",
                param => param.Add(new SqlParameter((!type.IsEnum && !needsId) ? type.GetProperties()[pkOrdinal].Name : "Id", id)),
                (reader, set) =>
                {
                    tableObj = DataMapper.MapToObject(reader, tableType);
                });

            _lastQueryExcuted = "dbo." + GetTableName(type) + "_Update";

            Query.ExecuteNonQuery(() => Connection, "dbo." + GetTableName(type) + "_Update",
                      param =>
                      {
                          PropertyInfo[] props = type.GetProperties();

                          if (needsId)
                              param.Add(new SqlParameter("Id", id));

                          foreach (PropertyInfo prop in props)
                          {
                              if (!needsId && prop == props[pkOrdinal])
                                  param.Add(new SqlParameter(prop.Name, id));
                              else if (prop.PropertyType.IsCollection())
                                  continue;
                              else if (prop.PropertyType.IsEnum)
                              {
                                  if (prop.GetValue(model) != null)
                                  {
                                      int enumId = prop.PropertyType.EnumToDictionary().Index(a => a.Key == (int)prop.GetValue(model)) + 1;
                                      param.Add(new SqlParameter(prop.Name, enumId));
                                  }
                                  else
                                      throw new Exception("Any property in model that is an Enum cannot be null");
                              }
                              else if (ShouldNormalize(prop.PropertyType))
                                  param.Add(new SqlParameter(prop.Name, tableObj.GetPropertyValue(prop.Name + "Id")));
                              else
                              {
                                  object value = null;

                                  if (model.GetPropertyValue(prop.Name) != null)
                                      value = model.GetPropertyValue(prop.Name);
                                  else
                                      value = DBNull.Value;

                                  param.Add(new SqlParameter(prop.Name, value));
                              }
                          }
                      });

            foreach (PropertyInfo prop in type.GetProperties())
            {
                if (ShouldNormalize(prop.PropertyType) && !prop.PropertyType.IsEnum)
                {
                    Update(model.GetPropertyValue(prop.Name), (int)tableObj.GetPropertyValue(prop.Name + "Id"), prop.PropertyType);
                }
                else if (prop.PropertyType.IsCollection())
                {
                    Type listType = prop.PropertyType.GetTypeOfT();

                    if (!listType.IsSystemType())
                    {
                        object[] list = model.GetPropertyValue(prop.Name) == null ? null : ((IEnumerable<object>)model.GetPropertyValue(prop.Name)).ToArray();
                        int[] ids = GetCollectionIds(id, type, listType);
                        int i = 0;

                        if (ids != null && ids.Length > 0)
                        {
                            foreach (int childId in ids)
                            {
                                if (list == null || list[i] == null)
                                {
                                    DeleteRelationship(type, listType, id, childId);
                                }
                                else
                                {
                                    Update(list[i], childId, listType);
                                }

                                i++;
                            }
                        }

                        if (list != null && list.Length > i)
                        {
                            for (; i < list.Length; i++)
                            {
                                object childId = Insert(list[i], listType);
                                InsertRelationship(type, listType, id, (int)childId);
                            }
                        }
                    }
                    else
                    {
                        string serializedObj = JsonConvert.SerializeObject(model.GetPropertyValue(prop.Name));
                        UpdateSerializedCollection(type, prop, id, serializedObj);
                    }
                }
            }
        }

        private void UpdateSerializedCollection(Type parentType, PropertyInfo property, object parentId, string serializedCollection)
        {
            string parentTypeName = parentType.Name.SafeName(),
                  childTypeName = property.PropertyType.GetTypeOfT().Name.SafeName();

            string collectionTbl = parentTypeName + '_' + property.Name + '_' + childTypeName + "Collections";
            Type parentIdType = parentId.GetType();
            Type listType = parentType.GetProperties().FirstOrDefault(a => a.PropertyType.IsCollection() && a == property).PropertyType;

            string query = _partialProcs["Update"].FormatString(collectionTbl)
                         + _partialProcs["Set"].FormatString("[Serialized" + childTypeName + "Collections] = '" + serializedCollection + "'")
                         + _partialProcs["Where"].FormatString(
                            ((parentIdType == typeof(string)) ? "CAST(" + parentTypeName + "Id AS VARCHAR(MAX)) = " : parentTypeName + "Id = ")
                            + ((parentIdType == typeof(string)) ? "'" + parentId + "'" : parentId)
                         );

            _lastQueryExcuted = query;

            Query.ExecuteNonQuery(
                    () => Connection
                   , query
                   , null
                   , null
                   , cmd => cmd.CommandType = CommandType.Text
                   , null);
        }

        #endregion Private Access Methods

        #region Public Access Methods

        public void Backup(string path = null)
        {
            try
            {
                if (path == null)
                {
                    path = Basic.GetOSDrive() + "ORMBackups";
                }

                path.CreateFolder();

                BackupDB(path);
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                {
                    _errorLog.Insert(new Error(ex));
                }

                throw ex;
            }
        }

        public void Delete(object id)
        {
            try
            {
                if (id.GetType() != IdType)
                    throw new Exception("id is not the right Type and cannot Delete...");

                Delete(_type, id);
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                    _errorLog.Insert(new Error(ex));

                throw ex;
            }
        }

        public void Delete(IEnumerable<object> ids)
        {
            try
            {
                if (ids == null)
                    throw new Exception("collection cannot be null to be able to Insert...");

                if (ids.Count() == 0)
                    throw new Exception("collection cannot be empty to be able to Insert...");

                foreach (object id in ids)
                    Delete(id);
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                    _errorLog.Insert(new Error(ex));

                throw ex;
            }
        }

        public object FirstOrDefault(Func<object, bool> predicate)
        {
            try
            {
                return Where(predicate).FirstOrDefault();
            }
            catch (Exception)
            {
                throw;
            }
        }

        public object Get(object id, Converter<object, object> converter)
        {
            try
            {
                if (id.GetType() != IdType)
                {
                    throw new Exception("id is not the right Type and cannot Get...");
                }

                return (converter == null)
                        ? Get(_type, id)
                        : converter(Get(_type, id));
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                {
                    _errorLog.Insert(new Error(ex));
                }

                throw ex;
            }
        }

        public object Get(object id)
        {
            try
            {
                return Get(id, null);
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                {
                    _errorLog.Insert(new Error(ex));
                }

                throw ex;
            }
        }

        public List<object> GetAll()
        {
            try
            {
                Dictionary<KeyValuePair<string, Type>, List<object>> container = new Dictionary<KeyValuePair<string, Type>, List<object>>();
                return GetAll(_type, ref container);
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                {
                    _errorLog.Insert(new Error(ex));
                }

                throw ex;
            }
        }

        public object Insert(object model)
        {
            try
            {
                if (model.GetType() != _type)
                    throw new Exception("model's Type has to be the type of T in DBService<T> to be able to Insert...");

                object id = null;
                Dictionary<KeyValuePair<Type, PropertyInfo>, KeyValuePair<object, object[]>> relations = new Dictionary<KeyValuePair<Type, PropertyInfo>, KeyValuePair<object, object[]>>();

                id = Insert(model, _type, ref relations);

                return id;
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                    _errorLog.Insert(new Error(ex));

                throw ex;
            }
        }

        public object Insert(object model, Converter<object, object> converter)
        {
            try
            {
                if (model.GetType() != _type)
                    throw new Exception("model's Type has to be the type of T in DBService<T> to be able to Insert...");

                object id = null;
                Dictionary<KeyValuePair<Type, PropertyInfo>, KeyValuePair<object, object[]>> relations = new Dictionary<KeyValuePair<Type, PropertyInfo>, KeyValuePair<object, object[]>>();

                id = Insert(converter(model), _type, ref relations);

                return id;
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                    _errorLog.Insert(new Error(ex));

                throw ex;
            }
        }

        public object[] Insert(IEnumerable<object> collection)
        {
            try
            {
                if (collection.GetTypeOfT() != _type)
                {
                    throw new Exception("model's Type has to be the type of T in DBService<T> to be able to Insert...");
                }

                if (collection.Count() == 0)
                {
                    throw new Exception("collection cannot be empty to be able to Insert...");
                }

                List<object> ids = new List<object>();
                Dictionary<KeyValuePair<Type, PropertyInfo>, KeyValuePair<object, object[]>> relations = new Dictionary<KeyValuePair<Type, PropertyInfo>, KeyValuePair<object, object[]>>();

                foreach (object model in collection)
                {
                    ids.Add(Insert(model, _type, ref relations));
                }

                return ids.ToArray();
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                {
                    _errorLog.Insert(new Error(ex));
                }

                throw ex;
            }
        }

        public object[] Insert(IEnumerable<object> collection, Converter<object, object> converter)
        {
            try
            {
                if (collection.GetTypeOfT() != _type)
                {
                    throw new Exception("model's Type has to be the type of T in DBService<T> to be able to Insert...");
                }

                if (collection.Count() == 0)
                {
                    throw new Exception("collection cannot be empty to be able to Insert...");
                }

                List<object> ids = new List<object>();
                Dictionary<KeyValuePair<Type, PropertyInfo>, KeyValuePair<object, object[]>> relations = new Dictionary<KeyValuePair<Type, PropertyInfo>, KeyValuePair<object, object[]>>();

                foreach (object model in collection)
                {
                    ids.Add(Insert(converter(model), _type, ref relations));
                }

                return ids.ToArray();
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                {
                    _errorLog.Insert(new Error(ex));
                }

                throw ex;
            }
        }

        public void Update(object model)
        {
            try
            {
                if (model.GetType() != _type)
                    throw new Exception("model's Type has to be the type of T in DBService<T> to be able to Update...");

                if (model.GetPropertyValue("Id") == null)
                    throw new Exception("model's Id propery has to equal an PK in the Database to be able to Update...");

                if (model.GetPropertyValue("Id").GetType() != IdType)
                    throw new Exception("model's Id propery has to equal the same Type as the Id column in the Database to be able to Update...");

                Update(model, model.GetPropertyValue("Id"), _type);
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                    _errorLog.Insert(new Error(ex));

                throw ex;
            }
        }

        public void Update(object model, Converter<object, object> converter)
        {
            try
            {
                if (model.GetType() != _type)
                    throw new Exception("model's Type has to be the type of T in DBService<T> to be able to Update...");

                if (model.GetPropertyValue("Id") == null)
                    throw new Exception("model's Id propery has to equal an PK in the Database to be able to Update...");

                if (model.GetPropertyValue("Id").GetType() != IdType)
                    throw new Exception("model's Id propery has to equal the same Type as the Id column in the Database to be able to Update...");

                Update(converter(model), model.GetPropertyValue("Id"), _type);
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                    _errorLog.Insert(new Error(ex));

                throw ex;
            }
        }

        public void Update(IEnumerable<object> collection)
        {
            try
            {
                if (collection.GetTypeOfT() != _type)
                {
                    throw new Exception("model's Type has to be the type of T in DBService<T> to be able to Update...");
                }

                if (collection.Count() == 0)
                {
                    throw new Exception("collection cannot be empty to be able to Update...");
                }

                if (collection.ElementAt(0).GetPropertyValue("Id") == null)
                {
                    throw new Exception("model's Id propery has to equal an PK in the Database to be able to Update...");
                }

                if (collection.ElementAt(0).GetPropertyValue("Id").GetType() != IdType)
                {
                    throw new Exception("model's Id propery has to equal the same Type as the Id column in the Database to be able to Update...");
                }

                foreach (object model in collection)
                {
                    Update(model, model.GetPropertyValue("Id"), _type);
                }
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                {
                    _errorLog.Insert(new Error(ex));
                }

                throw ex;
            }
        }

        public void Update(IEnumerable<object> collection, Converter<object, object> converter)
        {
            try
            {
                if (collection.GetTypeOfT() != _type)
                {
                    throw new Exception("model's Type has to be the type of T in DBService<T> to be able to Update...");
                }

                if (collection.Count() == 0)
                {
                    throw new Exception("collection cannot be empty to be able to Update...");
                }

                if (collection.ElementAt(0).GetPropertyValue("Id") == null)
                {
                    throw new Exception("model's Id propery has to equal an PK in the Database to be able to Update...");
                }

                if (collection.ElementAt(0).GetPropertyValue("Id").GetType() != IdType)
                {
                    throw new Exception("model's Id propery has to equal the same Type as the Id column in the Database to be able to Update...");
                }

                foreach (object model in collection)
                {
                    Update(converter(model), model.GetPropertyValue("Id"), _type);
                }
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                {
                    _errorLog.Insert(new Error(ex));
                }

                throw ex;
            }
        }

        public List<object> Where(Func<object, bool> predicate)
        {
            try
            {
                List<object> result = GetAll();
                if (result != null)
                {
                    result = result.Where(predicate).ToList();
                }
                else
                {
                    result = new List<object>();
                }

                return result;
            }
            catch (Exception ex)
            {
                if (_errorLog != null)
                {
                    _errorLog.Insert(new Error(ex));
                }

                throw ex;
            }
        }

        public static List<dynamic> QueryResults(string connectionString, string query, Dictionary<string, object> parameters)
        {
            List<dynamic> result = new List<dynamic>();

            void getRow(IDataReader reader, short set)
            {
                if (set >= 1)
                {
                    if (set == 1)
                    {
                        List<dynamic> oldResults = result;
                        result = new List<dynamic> { new List<dynamic>() };
                        foreach (dynamic obj in oldResults)
                            ((List<dynamic>)result[0]).Add(obj);
                    }

                    result.Add(new List<dynamic>());

                    var dataRow = new ExpandoObject() as IDictionary<string, object>;
                    for (var fieldCount = 0; fieldCount < reader.FieldCount; fieldCount++)
                        dataRow.Add(reader.GetName(fieldCount), reader[fieldCount]);

                    ((List<dynamic>)result[set]).Add(dataRow);
                }
                else
                {
                    var dataRow = new ExpandoObject() as IDictionary<string, object>;
                    for (var fieldCount = 0; fieldCount < reader.FieldCount; fieldCount++)
                        dataRow.Add(reader.GetName(fieldCount), reader[fieldCount]);

                    result.Add(dataRow);
                }
            }

            void setParams(SqlParameterCollection coll)
            {
                foreach (KeyValuePair<string, object> param in parameters)
                    coll.Add(new SqlParameter(param.Key, param.Value));
            }

            Query.ExecuteCmd(() => new SqlConnection(connectionString), query, setParams, getRow, null, mod => mod.CommandType = CommandType.Text);

            return result;
        }

        public List<dynamic> QueryResults(string query, Dictionary<string, object> parameters)
        {
            return QueryResults(Connection.ConnectionString, query, parameters);
        }

        #endregion Public Access Methods
    }

    public class DBService<T> : IDBService<T> where T : class
    {
        public DBService()
        {
            _baseSrv = new DBService(typeof(T));
        }

        public DBService(string connectionKey)
        {
            _baseSrv = new DBService(typeof(T), connectionKey);
        }

        public DBService(ORMOptions options)
        {
            _baseSrv = new DBService(typeof(T), options);
        }

        private DBService _baseSrv = null;

        internal Type IdType => _baseSrv.IdType;

        public void Backup(string path = null)
        {
            _baseSrv.Backup(path);
        }

        public void Delete(object id)
        {
            _baseSrv.Delete(id);
        }

        public void Delete(IEnumerable<object> ids)
        {
            if (ids == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            if (ids.Count() == 0)
            {
                throw new Exception("collection cannot be empty to be able to Insert...");
            }

            foreach (object id in ids)
            {
                Delete(id);
            }
        }

        public T FirstOrDefault(Func<T, bool> predicate)
        {
            return Where(predicate).FirstOrDefault();
        }

        public T Get(object id)
        {
            return Get(id, null);
        }

        public T Get(object id, Converter<T, T> converter)
        {
            T result = default(T);

            object item = _baseSrv.Get(id);

            result = (item == null)
                        ? null
                        : (converter == null)
                        ? (T)item
                        : converter((T)item);

            return result;
        }

        public List<T> GetAll()
        {
            Type listType = null;
            List<T> result = null;
            List<object> list = _baseSrv.GetAll();

            if (list != null)
            {
                if (list.Count > 0)
                {
                    listType = list[0].GetType();
                }

                if (listType != typeof(T))
                {
                    throw new Exception("objects in list are not the right Type of entity to access..");
                }

                if (result == null)
                {
                    result = list.Cast<T>().ToList();
                }
            }

            return result;
        }

        public object Insert(T model)
        {
            return _baseSrv.Insert(model);
        }

        public object Insert(T model, Converter<T, T> converter)
        {
            if (model == null)
            {
                throw new Exception("model cannot be null to be able to Insert...");
            }

            return Insert(converter(model));
        }

        public object[] Insert(IEnumerable<T> collection)
        {
            if (collection == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            if (collection.Count() == 0)
            {
                throw new Exception("collection cannot be empty to be able to Insert...");
            }

            List<object> list = new List<object>();
            foreach (T model in collection)
            {
                list.Add(Insert(model));
            }

            return list.ToArray();
        }

        public object[] Insert(IEnumerable<T> collection, Converter<T, T> converter)
        {
            if (collection == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            if (collection.Count() == 0)
            {
                throw new Exception("collection cannot be empty to be able to Insert...");
            }

            List<object> list = new List<object>();
            foreach (T model in collection)
            {
                list.Add(Insert(converter(model)));
            }

            return list.ToArray();
        }

        public void Update(T model)
        {
            _baseSrv.Update(model);
        }

        public void Update(T model, Converter<T, T> converter)
        {
            Update(converter(model));
        }

        public void Update(IEnumerable<T> collection)
        {
            if (collection == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            if (collection.Count() == 0)
            {
                throw new Exception("collection cannot be empty to be able to Insert...");
            }

            foreach (T model in collection)
            {
                Update(model);
            }
        }

        public void Update(IEnumerable<T> collection, Converter<T, T> converter)
        {
            if (collection == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            if (collection.Count() == 0)
            {
                throw new Exception("collection cannot be empty to be able to Insert...");
            }

            foreach (T model in collection)
            {
                Update(converter(model));
            }
        }

        public List<T> Where(Func<T, bool> predicate)
        {
            //TSqlFormatter.Format(predicate.ToExpression()).Log();

            List<T> result = GetAll();
            if (result != null)
            {
                result = result.Where(predicate).ToList();
            }
            else
            {
                result = new List<T>();
            }

            return result;
        }

        public List<TResult> QueryResults<TResult>(string query, Dictionary<string, object> parameters)
        {
            List<TResult> result = null;
            var queryResults = _baseSrv.QueryResults(query, parameters);
            foreach (var r in queryResults)
            {
                TResult record = Data.Map<TResult>(r);

                if (result == null)
                    result = new List<TResult>();

                result.Add(record);
            }

            return result;
        }
    }

    public class DBService<T, IdType> : IDBService<T, IdType> where T : class
    {
        public DBService()
        {
            _baseSrv = new DBService<T>();

            if (typeof(IdType) != _baseSrv.IdType)
            {
                throw new Exception("Specified IdType for model is not the right type... Expecting type of " + nameof(_baseSrv.IdType));
            }
        }

        public DBService(ORMOptions options)
        {
            _baseSrv = new DBService<T>(options);

            if (typeof(IdType) != _baseSrv.IdType)
            {
                throw new Exception("Specified IdType for model is not the right type... Expecting type of " + nameof(_baseSrv.IdType));
            }
        }

        public DBService(string connectionKey)
        {
            _baseSrv = new DBService<T>(connectionKey);

            if (typeof(IdType) != _baseSrv.IdType)
            {
                throw new Exception("Specified IdType for model is not the right type... Expecting type of " + nameof(_baseSrv.IdType));
            }
        }

        private DBService<T> _baseSrv = null;

        public void Backup(string path = null)
        {
            _baseSrv.Backup(path);
        }

        public void Delete(IdType id)
        {
            _baseSrv.Delete(id);
        }

        public void Delete(IEnumerable<IdType> ids)
        {
            if (ids == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            if (ids.Count() == 0)
            {
                throw new Exception("collection cannot be empty to be able to Insert...");
            }

            foreach (IdType id in ids)
            {
                Delete(id);
            }
        }

        public T FirstOrDefault(Func<T, bool> predicate)
        {
            return Where(predicate).FirstOrDefault();
        }

        public T Get(IdType id, Converter<T, T> converter)
        {
            return _baseSrv.Get(id, converter);
        }

        public T Get(IdType id)
        {
            return Get(id, null);
        }

        public List<T> GetAll()
        {
            List<T> result = null;
            Type listType = null;
            List<T> list = _baseSrv.GetAll();

            if (list != null)
            {
                if (list.Count > 0)
                {
                    listType = list[0].GetType();
                }

                if (listType != typeof(T))
                {
                    throw new Exception("objects in list are not the right Type of entity to access..");
                }

                if (result == null)
                {
                    result = list.Cast<T>().ToList();
                }
                //foreach (object item in list)
                //    result.Add((T)item);
            }

            return result;
        }

        public IdType Insert(T model)
        {
            IdType result = default(IdType);

            object id = _baseSrv.Insert(model);

            if (id.GetType() != typeof(IdType))
            {
                throw new Exception("id is not the right Type...");
            }

            result = (IdType)id;

            return result;
        }

        public IdType Insert(T model, Converter<T, T> converter)
        {
            if (model == null)
            {
                throw new Exception("model cannot be null to be able to Insert...");
            }

            return Insert(converter(model));
        }

        public IdType[] Insert(IEnumerable<T> collection)
        {
            if (collection == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            if (collection.Count() == 0)
            {
                throw new Exception("collection cannot be empty to be able to Insert...");
            }

            List<IdType> list = new List<IdType>();
            foreach (T model in collection)
            {
                list.Add(Insert(model));
            }

            return list.ToArray();
        }

        public IdType[] Insert(IEnumerable<T> collection, Converter<T, T> converter)
        {
            if (collection == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            if (collection.Count() == 0)
            {
                throw new Exception("collection cannot be empty to be able to Insert...");
            }

            List<IdType> list = new List<IdType>();
            foreach (T model in collection)
            {
                list.Add(Insert(converter(model)));
            }

            return list.ToArray();
        }

        public void Update(T model)
        {
            _baseSrv.Update(model);
        }

        public void Update(IEnumerable<T> collection)
        {
            if (collection == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            if (collection.Count() == 0)
            {
                throw new Exception("collection cannot be empty to be able to Insert...");
            }

            foreach (T model in collection)
            {
                Update(model);
            }
        }

        public void Update(IEnumerable<T> collection, Converter<T, T> converter)
        {
            if (collection == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            if (collection.Count() == 0)
            {
                throw new Exception("collection cannot be empty to be able to Insert...");
            }

            foreach (T model in collection)
            {
                Update(converter(model));
            }
        }

        public void Update(T model, Converter<T, T> converter)
        {
            if (model == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            Update(converter(model));
        }

        public List<T> Where(Func<T, bool> predicate)
        {
            //var exp = predicate.ToExpression();
            //TSqlFormatter.Format(exp, true).Log();

            List<T> result = GetAll();
            if (result != null)
            {
                result = result.Where(predicate).ToList();
            }
            else
            {
                result = new List<T>();
            }

            return result;
        }

        public List<TResult> QueryResults<TResult>(string query, Dictionary<string, object> parameters)
        {
            return _baseSrv.QueryResults<TResult>(query, parameters); ;
        }
    }

    public class DBService<T, IdType, AddType, UpdateType> : IDBService<T, IdType, AddType, UpdateType> where T : class
    {
        public DBService()
        {
            _baseSrv = new DBService<T, IdType>();
        }

        public DBService(string connectionKey)
        {
            _baseSrv = new DBService<T, IdType>(connectionKey);
        }

        public DBService(ORMOptions options)
        {
            _baseSrv = new DBService<T, IdType>(options);
        }

        private DBService<T, IdType> _baseSrv = null;

        public void Backup(string path = null)
        {
            _baseSrv.Backup(path);
        }

        public void Delete(IdType id)
        {
            _baseSrv.Delete(id);
        }

        public void Delete(IEnumerable<IdType> ids)
        {
            if (ids == null)
            {
                throw new Exception("collection cannot be null to be able to Insert...");
            }

            if (ids.Count() == 0)
            {
                throw new Exception("collection cannot be empty to be able to Insert...");
            }

            foreach (IdType id in ids)
            {
                Delete(id);
            }
        }

        public T FirstOrDefault(Func<T, bool> predicate)
        {
            return Where(predicate).FirstOrDefault();
        }

        public T Get(IdType id, Converter<T, T> converter)
        {
            return _baseSrv.Get(id, converter);
        }

        public T Get(IdType id)
        {
            return Get(id, null);
        }

        public List<T> GetAll()
        {
            List<T> result = null;
            Type listType = null;
            List<T> list = _baseSrv.GetAll();

            if (list != null)
            {
                if (list.Count > 0)
                {
                    listType = list[0].GetType();
                }

                if (listType != typeof(T))
                {
                    throw new Exception("objects in list are not the right Type of entity to access..");
                }

                if (result == null)
                {
                    result = list.Cast<T>().ToList();
                }
            }

            return result;
        }

        public IdType Insert(T model)
        {
            IdType result = default(IdType);

            object id = _baseSrv.Insert(model);

            if (id.GetType() != typeof(IdType))
            {
                throw new Exception("id is not the right Type...");
            }

            result = (IdType)id;

            return result;
        }

        public IdType Insert(AddType model, Converter<AddType, T> converter)
        {
            return Insert(converter(model));
        }

        public IdType Insert(T model, Converter<T, T> converter)
        {
            throw new NotImplementedException();
        }

        public IdType[] Insert(IEnumerable<T> collection)
        {
            throw new NotImplementedException();
        }

        public IdType[] Insert(IEnumerable<T> collection, Converter<T, T> converter)
        {
            throw new NotImplementedException();
        }

        public void Update(T model)
        {
            _baseSrv.Update(model);
        }

        public void Update(UpdateType model, Converter<UpdateType, T> converter)
        {
            Update(converter(model));
        }

        public void Update(IEnumerable<T> collection)
        {
            throw new NotImplementedException();
        }

        public void Update(IEnumerable<T> collection, Converter<T, T> converter)
        {
            throw new NotImplementedException();
        }

        public void Update(T model, Converter<T, T> converter)
        {
            throw new NotImplementedException();
        }

        public List<T> Where(Func<T, bool> predicate)
        {
            //Expression<Func<T, bool>> exp = x => predicate(x);
            //TSqlFormatter.Format(exp).Log();

            List<T> result = GetAll();
            if (result != null)
            {
                result = result.Where(predicate).ToList();
            }
            else
            {
                result = new List<T>();
            }

            return result;
        }

        public List<TResult> QueryResults<TResult>(string query, Dictionary<string, object> parameters)
        {
            return _baseSrv.QueryResults<TResult>(query, parameters); ;
        }
    }
}