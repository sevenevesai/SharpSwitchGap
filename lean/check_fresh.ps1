param([string]$Audit = 'SharpSwitchGap/B1Checks.lean')

# Remove only our generated Lean artifacts; retain pinned upstream and Mathlib builds.
$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath $PSScriptRoot
$env:LEAN_NUM_THREADS = '4'
foreach ($relative in @('.lake/build/lib/lean', '.lake/build/ir')) {
    $artifactRoot = (Resolve-Path -LiteralPath $relative).Path
    foreach ($artifact in Get-ChildItem -LiteralPath $artifactRoot -Filter 'SharpSwitchGap*') {
        $resolvedArtifact = (Resolve-Path -LiteralPath $artifact.FullName).Path
        if (-not $resolvedArtifact.StartsWith($artifactRoot + '\',
                [StringComparison]::OrdinalIgnoreCase)) {
            throw "Artifact outside expected build directory: $resolvedArtifact"
        }
        if ($artifact.Attributes -band [IO.FileAttributes]::ReparsePoint) {
            throw "Refusing to remove a reparse point: $resolvedArtifact"
        }
        Remove-Item -LiteralPath $resolvedArtifact -Recurse -Force
    }
}
$buildTimer = [Diagnostics.Stopwatch]::StartNew()
& lake build
$buildExit = $LASTEXITCODE
$buildTimer.Stop()
Write-Output ('Fresh lake build: exit {0}, {1:F2} s' -f $buildExit, $buildTimer.Elapsed.TotalSeconds)
if ($buildExit -ne 0) { exit $buildExit }
$auditTimer = [Diagnostics.Stopwatch]::StartNew()
& lake env lean $Audit
$auditExit = $LASTEXITCODE
$auditTimer.Stop()
Write-Output ('Axiom audit: exit {0}, {1:F2} s' -f $auditExit, $auditTimer.Elapsed.TotalSeconds)
exit $auditExit
