param(
    [Parameter(Mandatory = $true)][string]$Evidence,
    [ValidateSet('native', 'candidate')][string]$Phase = 'native'
)
$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest
$Utf8 = [System.Text.UTF8Encoding]::new($false)
Add-Type -TypeDefinition @'
using System;
using System.Runtime.InteropServices;
using System.Text;

public sealed class NativeNamespaceRecord {
    public string Input = "";
    public string InputUtf16 = "";
    public string FinalPath = "";
    public string FinalPathUtf16 = "";
    public string Identity = "";
    public string FailedApi = "";
    public int Error = 0;
    public int CloseError = 0;
    public uint Attributes = 0;
    public uint FinalPathLength = 0;
    public bool Success = false;
}

public static class RawNamespaceR36 {
    [StructLayout(LayoutKind.Sequential)]
    private struct NativeFileTime { public uint Low; public uint High; }
    [StructLayout(LayoutKind.Sequential)]
    private struct NativeInformation {
        public uint Attributes;
        public NativeFileTime Creation;
        public NativeFileTime Access;
        public NativeFileTime Write;
        public uint VolumeSerial;
        public uint FileSizeHigh;
        public uint FileSizeLow;
        public uint Links;
        public uint FileIndexHigh;
        public uint FileIndexLow;
    }
    [DllImport("kernel32.dll", CharSet = CharSet.Unicode, SetLastError = true, ExactSpelling = true)]
    [return: MarshalAs(UnmanagedType.Bool)]
    private static extern bool CreateDirectoryW(string name, IntPtr security);
    [DllImport("kernel32.dll", CharSet = CharSet.Unicode, SetLastError = true, ExactSpelling = true)]
    private static extern IntPtr CreateFileW(string name, uint access, uint sharing,
        IntPtr security, uint disposition, uint flags, IntPtr template);
    [DllImport("kernel32.dll", SetLastError = true, ExactSpelling = true)]
    [return: MarshalAs(UnmanagedType.Bool)]
    private static extern bool GetFileInformationByHandle(IntPtr handle, out NativeInformation information);
    [DllImport("kernel32.dll", CharSet = CharSet.Unicode, SetLastError = true, ExactSpelling = true)]
    private static extern uint GetFinalPathNameByHandleW(IntPtr handle, StringBuilder path, uint length, uint flags);
    [DllImport("kernel32.dll", SetLastError = true, ExactSpelling = true)]
    [return: MarshalAs(UnmanagedType.Bool)]
    private static extern bool CloseHandle(IntPtr handle);

    public static string Hex(string value) {
        StringBuilder result = new StringBuilder(value.Length * 4);
        foreach (char unit in value) result.Append(((ushort)unit).ToString("x4"));
        return result.ToString();
    }

    public static int Create(string path) {
        if (CreateDirectoryW(path, IntPtr.Zero)) return 0;
        return Marshal.GetLastWin32Error();
    }

    public static NativeNamespaceRecord Open(string path) {
        NativeNamespaceRecord result = new NativeNamespaceRecord();
        result.Input = path;
        result.InputUtf16 = Hex(path);
        IntPtr handle = CreateFileW(path, 0, 7, IntPtr.Zero, 3, 0x02000000, IntPtr.Zero);
        if (handle == new IntPtr(-1)) {
            result.FailedApi = "CreateFileW";
            result.Error = Marshal.GetLastWin32Error();
            return result;
        }
        try {
            NativeInformation information;
            if (!GetFileInformationByHandle(handle, out information)) {
                result.FailedApi = "GetFileInformationByHandle";
                result.Error = Marshal.GetLastWin32Error();
                return result;
            }
            result.Attributes = information.Attributes;
            result.Identity = information.VolumeSerial.ToString("x8") + ":" +
                information.FileIndexHigh.ToString("x8") + ":" + information.FileIndexLow.ToString("x8");
            StringBuilder finalPath = new StringBuilder(32768);
            uint length = GetFinalPathNameByHandleW(handle, finalPath, (uint)finalPath.Capacity, 0);
            result.FinalPathLength = length;
            if (length == 0) {
                result.FailedApi = "GetFinalPathNameByHandleW";
                result.Error = Marshal.GetLastWin32Error();
                return result;
            }
            if (length >= finalPath.Capacity) {
                result.FailedApi = "GetFinalPathNameByHandleW:buffer";
                result.Error = 122;
                return result;
            }
            result.FinalPath = finalPath.ToString();
            result.FinalPathUtf16 = Hex(result.FinalPath);
            result.Success = true;
            return result;
        } finally {
            if (!CloseHandle(handle)) {
                result.CloseError = Marshal.GetLastWin32Error();
                result.Success = false;
            }
        }
    }
}
'@

function Save-Json([string]$Name, [object]$Value) {
    [System.IO.File]::WriteAllText(($Evidence + '\' + $Name), ($Value | ConvertTo-Json -Depth 15) + [Environment]::NewLine, $Utf8)
}

if ($Phase -eq 'native') {
    $Temp = $env:RUNNER_TEMP.TrimEnd([char]'\')
    if ($Temp -cnotmatch '^[A-Za-z]:\\') { throw 'The native fixture requires an absolute local drive path.' }
    $Ordinary = $Temp + '\emd-namespace-r36-' + $env:GITHUB_RUN_ID + '-' + $env:GITHUB_RUN_ATTEMPT
    $Verbatim = '\\?\' + $Ordinary
    $Creations = [System.Collections.Generic.List[object]]::new()
    $Fixtures = [System.Collections.Generic.List[object]]::new()
    $Names = @(
        @{ Id = 'trimmed'; Name = 'assets' },
        @{ Id = 'dot'; Name = 'assets.' },
        @{ Id = 'space'; Name = 'assets ' }
    )
    $CreationPaths = [System.Collections.Generic.List[string]]::new()
    $CreationPaths.Add($Verbatim)
    foreach ($Name in $Names) {
        $CreationPaths.Add($Verbatim + '\' + $Name.Name)
        $CreationPaths.Add($Verbatim + '\' + $Name.Name + '\child')
    }
    foreach ($Path in $CreationPaths) {
        $ErrorCode = [RawNamespaceR36]::Create($Path)
        $Creations.Add(@{ path = $Path; utf16 = [RawNamespaceR36]::Hex($Path); error = $ErrorCode })
        if ($ErrorCode -ne 0) {
            Save-Json 'creations.json' $Creations.ToArray()
            throw "CreateDirectoryW failed with native error $ErrorCode"
        }
    }
    foreach ($Name in $Names) {
        foreach ($Position in @('final', 'intermediate')) {
            $Path = $Verbatim + '\' + $Name.Name
            if ($Position -eq 'intermediate') { $Path += '\child' }
            $Record = [RawNamespaceR36]::Open($Path)
            $Fixture = @{ id = ($Name.Id + '-' + $Position); native = $Record }
            $Fixtures.Add($Fixture)
            Write-Output ('FIXTURE_IDENTITY ' + ($Fixture | ConvertTo-Json -Compress -Depth 12))
            if (-not $Record.Success -or ($Record.Attributes -band 16) -eq 0) {
                Save-Json 'fixtures.json' $Fixtures.ToArray()
                throw 'A raw verbatim fixture could not be identified as a directory.'
            }
        }
    }
    if (@($Fixtures | ForEach-Object { $_.native.Identity } | Sort-Object -Unique).Count -ne 6) {
        throw 'The three literal/trimmed siblings and their children are not six distinct native identities.'
    }
    $Prefixes = @(
        @{ Id = 'ordinary'; Root = $Ordinary },
        @{ Id = 'device'; Root = ('\\.\' + $Ordinary) },
        @{ Id = 'verbatim'; Root = $Verbatim }
    )
    $Cases = [System.Collections.Generic.List[object]]::new()
    foreach ($Prefix in $Prefixes) {
        foreach ($Suffix in @(@{ Id = 'dot'; Text = '.' }, @{ Id = 'space'; Text = ' ' })) {
            foreach ($Position in @('final', 'intermediate')) {
                $Path = $Prefix.Root + '\assets' + $Suffix.Text
                if ($Position -eq 'intermediate') { $Path += '\child' }
                if ($Path.EndsWith('\', [StringComparison]::Ordinal)) { throw 'A tested operand unexpectedly has a trailing separator.' }
                $Record = [RawNamespaceR36]::Open($Path)
                $Matches = @($Fixtures | Where-Object { $_.native.Identity -ceq $Record.Identity } | ForEach-Object { $_.id })
                $Case = @{
                    id = ($Prefix.Id + '-' + $Suffix.Id + '-' + $Position)
                    prefix = $Prefix.Id; suffix = $Suffix.Id; position = $Position
                    input = $Path; native = $Record; matched_fixture_ids = $Matches
                }
                $Cases.Add($Case)
                Write-Output ('NATIVE_NAMESPACE ' + ($Case | ConvertTo-Json -Compress -Depth 12))
            }
        }
    }
    $Report = @{
        oracle = 'Raw CreateFileW, GetFileInformationByHandle, GetFinalPathNameByHandleW'
        powershell = $PSVersionTable.PSVersion.ToString()
        os = [Environment]::OSVersion.VersionString
        raw_api_only_for_fixture_paths = $true
        creations = $Creations.ToArray(); fixtures = $Fixtures.ToArray(); cases = $Cases.ToArray()
    }
    Save-Json 'native.json' $Report
    $Tsv = ($Cases | ForEach-Object { $_.id + "`t" + $_.input }) -join "`n"
    [System.IO.File]::WriteAllText(($Evidence + '\cases.tsv'), $Tsv + "`n", $Utf8)
    if ($Cases.Count -ne 12) { throw 'The frozen matrix did not produce exactly twelve observations.' }
    Write-Output 'NATIVE_NAMESPACE_COMPLETE cases=12 fixtures=6'
} else {
    $Original = Get-Content -LiteralPath ($Evidence + '\native.json') -Raw | ConvertFrom-Json
    $Rust = @(Get-Content -LiteralPath ($Evidence + '\rust-results.json') -Raw | ConvertFrom-Json)
    $Results = [System.Collections.Generic.List[object]]::new()
    foreach ($Case in $Original.cases) {
        $Rows = @($Rust | Where-Object { $_.id -ceq $Case.id })
        if ($Rows.Count -ne 1 -or $Rows[0].input -cne $Case.input) { throw 'Rust observation identity mismatch.' }
        $Row = $Rows[0]
        $Native = $null
        if ($Row.status -ceq 'ok') { $Native = [RawNamespaceR36]::Open($Row.resolved) }
        $Same = $false
        if ($null -ne $Native -and $Native.Success -and $Case.native.Success) {
            $Same = $Native.Identity -ceq $Case.native.Identity
        }
        $Comparison = @{ id = $Case.id; raw_input = $Case.input; oracle = $Case.native; rust = $Row; resolved_native = $Native; same_native_identity = $Same }
        $Results.Add($Comparison)
        Write-Output ('CANDIDATE_NAMESPACE ' + ($Comparison | ConvertTo-Json -Compress -Depth 15))
    }
    if ($Results.Count -ne 12) { throw 'The candidate comparison did not produce twelve observations.' }
    Save-Json 'candidate-observations.json' $Results.ToArray()
    Write-Output 'CANDIDATE_NAMESPACE_COMPLETE cases=12'
}
