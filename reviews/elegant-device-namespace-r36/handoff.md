# Raw Windows namespace observation r36

This isolated Depot Windows job records raw API results before changing either engine.

- Source commit: b60c42d2b887e5c3de048c9bdd3828e51665a9d8
- Source tree: 728e8e818219a1c73441d78e4d212a09a5cec900, 6,714 tracked blobs.
- Maintained PR28 head: 98ef933e487f502e2e3555750e6621291ba21601.
- Actual main: afa5a631ec41cb1e9aa0634b2d547d084bd27e33.
- The full paired proof at 05a80ea47ba66d67fceb29b767caca6449fbb60d remains unlaunched.

Raw CreateDirectoryW creates trimmed, dot-suffixed and space-suffixed siblings and a child in each. Raw CreateFileW plus GetFileInformationByHandle and GetFinalPathNameByHandleW proves their six identities are distinct and observes twelve operands: ordinary/device/verbatim prefix, dot/space suffix, final/intermediate position. No operand ends in a separator. Native errors remain records; no mapping is assumed.

A standalone Rust test then invokes the unchanged candidate resolver for those exact operands. Returned paths are opened through the same native API, and identity comparisons remain observations. All candidate blobs and index modes are verified before and after temporary test insertion. No repository build or repository-wide gate is run. No production source is changed.

The manifest binds every proof file and the complete source index. Executables stay outside the uploaded evidence; their SHA-256 values are recorded. Previous r33/r34 failures and the frozen original four witnesses are unchanged.

File SHA-256 values:
- native.ps1: 129baede5a874c8f357a3152603fec49ad33d8daa2d56049c48b590980bef54b
- namespace-observer.rs: 8ca35cc8cdf40b7f96ed43b6cea15786621a5c1fe61344dc3c2332b6f7f0e0e7
- verify.py: 9d0f8d8b921a4c154f8e97bc6cfda804a1b36f1bcd7a3af9647a32b5ae21ed66
- manifest.json: 2e4205763466f661edbeaae4ab250ad4a455a005b1f209c6e2ca9fcbfb5644d0
- workflow.yml: 64b4d5fe644ae8a95f3c3817c63330eae6a06911a945dfbb6e898f0f1b87e2dc

This is an observation harness. Successful completion does not assert that the candidate matches Windows for every case.
