using System;
using Nostreets.Extensions.DataControl.Classes;
using Nostreets.Extensions.Interfaces;

namespace Nostreets.Orm.Ado
{
    public class ORMOptions
    {
        public static bool HasWipedDB { get; set; } = false;

        public bool WipeDB { get; set; } = false;

        public bool NullLock { get; set; } = false;

        public string ConnectionKey { get; set; } = "DefaultConnection";

        public IDBService<Error> ErrorLog { get; set; } = null;

    }
}
