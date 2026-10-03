// Portable, fixed-policy Windows console argv bridge. No compiler or trace logic.
// The launcher must bind this source/executable AND the exact policy file to its
// strong adaptation trace. The bridge accepts no PATH lookup and launches no shell.
using System;
using System.Collections.Generic;
using System.IO;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using System.Web.Script.Serialization;

internal static class DispatchBridge309 {
    private const string PolicyEnv = "LAKEFRONT309_BRIDGE_POLICY";
    private const string PolicyShaEnv = "LAKEFRONT309_BRIDGE_POLICY_SHA256";
    private static readonly UTF8Encoding StrictUtf8 = new UTF8Encoding(false, true);

    [StructLayout(LayoutKind.Sequential)] private struct StartupInfo {
        public uint cb;
        public IntPtr reserved, desktop, title;
        public uint x, y, xSize, ySize, xChars, yChars, fill, flags;
        public ushort show, reservedBytes;
        public IntPtr reservedData, stdin, stdout, stderr;
    }
    [StructLayout(LayoutKind.Sequential)] private struct StartupInfoEx {
        public StartupInfo basic;
        public IntPtr attributes;
    }
    [StructLayout(LayoutKind.Sequential)] private struct ProcessInformation {
        public IntPtr process, thread;
        public uint pid, tid;
    }
    [DllImport("kernel32", SetLastError=true)] private static extern IntPtr GetStdHandle(int selector);
    [DllImport("kernel32")] private static extern IntPtr GetCurrentProcess();
    [DllImport("kernel32", SetLastError=true)] private static extern bool DuplicateHandle(IntPtr sourceProcess, IntPtr source,
        IntPtr targetProcess, out IntPtr target, uint access, bool inherit, uint flags);
    [DllImport("kernel32", SetLastError=true)] private static extern bool CloseHandle(IntPtr handle);
    [DllImport("kernel32", SetLastError=true)] private static extern bool InitializeProcThreadAttributeList(
        IntPtr list, int count, int flags, ref IntPtr bytes);
    [DllImport("kernel32", SetLastError=true)] private static extern bool UpdateProcThreadAttribute(IntPtr list,
        uint flags, IntPtr attribute, IntPtr value, IntPtr size, IntPtr previous, IntPtr returned);
    [DllImport("kernel32")] private static extern void DeleteProcThreadAttributeList(IntPtr list);
    [DllImport("kernel32", CharSet=CharSet.Unicode, SetLastError=true)] private static extern bool CreateProcessW(
        string application, StringBuilder command, IntPtr processAttributes, IntPtr threadAttributes,
        bool inheritHandles, uint flags, IntPtr environment, string cwd,
        ref StartupInfoEx startup, out ProcessInformation child);
    [DllImport("kernel32", SetLastError=true)] private static extern uint WaitForSingleObject(IntPtr handle, uint timeout);
    [DllImport("kernel32", SetLastError=true)] private static extern bool GetExitCodeProcess(IntPtr handle, out uint code);

    private static void WinCheck(bool ok, string stage) {
        if (!ok) throw new System.ComponentModel.Win32Exception(Marshal.GetLastWin32Error(), stage);
    }

    private static int LaunchExact(string python, string arguments) {
        // Explicit Win64 ABI, verified before any process creation. No shell or
        // ProcessStartInfo handle inheritance; only the three duplicate standard
        // handles are inherited, so the caller's pipe writer cannot leak to a child.
        if (IntPtr.Size != 8 || Marshal.SizeOf(typeof(StartupInfo)) != 104 ||
            Marshal.SizeOf(typeof(StartupInfoEx)) != 112 || Marshal.SizeOf(typeof(ProcessInformation)) != 24 ||
            Marshal.OffsetOf(typeof(StartupInfo), "stdin").ToInt32() != 80)
            throw new InvalidDataException("unexpected native Win64 process ABI");
        var startup = new StartupInfoEx();
        startup.basic.cb = 112;
        startup.basic.flags = 0x100; // STARTF_USESTDHANDLES
        var streams = new IntPtr[3];
        IntPtr storage = IntPtr.Zero;
        bool initialized = false;
        var child = new ProcessInformation();
        try {
            for (int i = 0; i < 3; ++i) {
                IntPtr original = GetStdHandle(-10 - i);
                if (original != IntPtr.Zero && original != new IntPtr(-1))
                    WinCheck(DuplicateHandle(GetCurrentProcess(), original, GetCurrentProcess(), out streams[i],
                        0, true, 2), "duplicate exact standard handle");
            }
            startup.basic.stdin = streams[0];
            startup.basic.stdout = streams[1];
            startup.basic.stderr = streams[2];
            var inherited = new List<IntPtr>();
            foreach (var stream in streams) if (stream != IntPtr.Zero) inherited.Add(stream);
            uint flags = 0x08000000; // CREATE_NO_WINDOW
            if (inherited.Count != 0) {
                IntPtr bytes = IntPtr.Zero;
                bool first = InitializeProcThreadAttributeList(IntPtr.Zero, 1, 0, ref bytes);
                if (first || bytes.ToInt64() <= 0 || Marshal.GetLastWin32Error() != 122)
                    throw new InvalidDataException("unexpected attribute-list allocation result");
                startup.attributes = Marshal.AllocHGlobal(bytes);
                WinCheck(InitializeProcThreadAttributeList(startup.attributes, 1, 0, ref bytes), "initialize handle whitelist");
                initialized = true;
                storage = Marshal.AllocHGlobal(IntPtr.Size * inherited.Count);
                for (int i = 0; i < inherited.Count; ++i) Marshal.WriteIntPtr(storage, i * IntPtr.Size, inherited[i]);
                WinCheck(UpdateProcThreadAttribute(startup.attributes, 0, new IntPtr(0x00020002), storage,
                    new IntPtr(IntPtr.Size * inherited.Count), IntPtr.Zero, IntPtr.Zero), "bind handle whitelist");
                flags |= 0x00080000; // EXTENDED_STARTUPINFO_PRESENT
            } else startup.basic.cb = 104;
            var command = new StringBuilder(Quote(python) + " " + arguments, 32767);
            WinCheck(CreateProcessW(python, command, IntPtr.Zero, IntPtr.Zero, inherited.Count != 0,
                flags, IntPtr.Zero, null, ref startup, out child), "CreateProcessW exact Python");
            CloseHandle(child.thread); child.thread = IntPtr.Zero;
            // Original parent handles remain untouched; only duplicates are closed.
            for (int i = 0; i < streams.Length; ++i) {
                if (streams[i] != IntPtr.Zero) { CloseHandle(streams[i]); streams[i] = IntPtr.Zero; }
            }
            if (WaitForSingleObject(child.process, 0xFFFFFFFF) != 0)
                throw new System.ComponentModel.Win32Exception(Marshal.GetLastWin32Error(), "wait exact Python process");
            uint exit;
            WinCheck(GetExitCodeProcess(child.process, out exit), "observe exact Python exit");
            return unchecked((int)exit);
        } finally {
            if (child.thread != IntPtr.Zero) CloseHandle(child.thread);
            if (child.process != IntPtr.Zero) CloseHandle(child.process);
            foreach (var stream in streams) if (stream != IntPtr.Zero) CloseHandle(stream);
            if (initialized) DeleteProcThreadAttributeList(startup.attributes);
            if (startup.attributes != IntPtr.Zero) Marshal.FreeHGlobal(startup.attributes);
            if (storage != IntPtr.Zero) Marshal.FreeHGlobal(storage);
        }
    }

    private static string Sha256(string path) {
        using (var stream = File.OpenRead(path))
        using (var hash = SHA256.Create()) {
            var bytes = hash.ComputeHash(stream);
            var text = new StringBuilder(64);
            foreach (byte value in bytes) text.Append(value.ToString("x2"));
            return text.ToString();
        }
    }

    private static bool IsSha(string value) {
        if (value == null || value.Length != 64) return false;
        foreach (char c in value)
            if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f'))) return false;
        return true;
    }

    private static string ExactFile(string value) {
        if (String.IsNullOrEmpty(value) || !Path.IsPathRooted(value))
            throw new InvalidDataException("policy requires an explicit absolute file");
        var root = Path.GetPathRoot(value);
        if (String.IsNullOrEmpty(root) || !root.EndsWith("\\", StringComparison.Ordinal))
            throw new InvalidDataException("drive-relative file path refused");
        var path = Path.GetFullPath(value);
        if (!File.Exists(path)) throw new FileNotFoundException("exact policy file missing", path);
        if ((File.GetAttributes(path) & FileAttributes.ReparsePoint) != 0)
            throw new InvalidDataException("policy file itself may not be a reparse point");
        return path;
    }

    // Windows CRT/Python rules: 2*n+1 backslashes before a literal quote;
    // 2*n before the closing quote; unchanged backslashes before ordinary text.
    private static string Quote(string value) {
        var result = new StringBuilder("\"");
        int slashes = 0;
        foreach (char c in value) {
            if (c == '\\') { ++slashes; continue; }
            if (c == '"') result.Append('\\', 2 * slashes + 1);
            else result.Append('\\', slashes);
            result.Append(c);
            slashes = 0;
        }
        result.Append('\\', 2 * slashes).Append('"');
        return result.ToString();
    }

    private static string Text(Dictionary<string, object> policy, string key) {
        object value;
        if (!policy.TryGetValue(key, out value) || !(value is string))
            throw new InvalidDataException("missing string policy field: " + key);
        return (string)value;
    }

    public static int Main(string[] args) {
        int childExit = 125;
        bool childObserved = false;
        try {
            string expectedPolicy = Environment.GetEnvironmentVariable(PolicyShaEnv);
            if (!IsSha(expectedPolicy)) throw new InvalidDataException("missing exact policy SHA256");
            string policyPath = ExactFile(Environment.GetEnvironmentVariable(PolicyEnv));
            if (Sha256(policyPath) != expectedPolicy) throw new InvalidDataException("policy SHA256 differs");
            var parser = new JavaScriptSerializer { MaxJsonLength = 16384, RecursionLimit = 8 };
            var policy = parser.DeserializeObject(StrictUtf8.GetString(File.ReadAllBytes(policyPath)))
                as Dictionary<string, object>;
            if (policy == null || policy.Count != 5 || Text(policy, "schema") != "lakefront309.bridge.v1")
                throw new InvalidDataException("unexpected bridge policy schema/fields");
            string python = ExactFile(Text(policy, "python"));
            string dispatcher = ExactFile(Text(policy, "dispatcher"));
            string pythonSha = Text(policy, "python_sha256");
            string dispatcherSha = Text(policy, "dispatcher_sha256");
            if (!IsSha(pythonSha) || !IsSha(dispatcherSha) ||
                Sha256(python) != pythonSha || Sha256(dispatcher) != dispatcherSha)
                throw new InvalidDataException("exact Python/dispatcher bytes differ");
            var parts = new List<string> { "-B", "-X", "utf8", dispatcher };
            parts.AddRange(args);
            var command = new StringBuilder();
            foreach (string part in parts) {
                if (command.Length != 0) command.Append(' ');
                command.Append(Quote(part));
            }
            if (command.Length >= 32700) throw new InvalidDataException("Windows command line too long");
            // Native null cwd/environment inherit the exact caller's values.
            childExit = LaunchExact(python, command.ToString());
            childObserved = true;
            if (Sha256(policyPath) != expectedPolicy || Sha256(python) != pythonSha ||
                Sha256(dispatcher) != dispatcherSha)
                throw new InvalidDataException("bridge bound files changed during child execution");
            // .NET's signed Int32 preserves the complete Windows DWORD exit bits.
            return childExit;
        } catch (Exception error) {
            Console.Error.WriteLine("DispatchBridge309 refused: " + error.GetType().Name + ": " + error.Message);
            return childObserved && childExit != 0 ? childExit : 125;
        }
    }
}
