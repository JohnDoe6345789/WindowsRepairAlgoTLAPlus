$Version = "1.8.0"
$Url = "https://github.com/tlaplus/tlaplus/releases/download/v$Version/tla2tools.jar"
$TargetDir = "tools"
$TargetFile = "$TargetDir/tla2tools.jar"

if (-not (Test-Path $TargetDir)) {
    New-Item -ItemType Directory -Path $TargetDir | Out-Null
}

if (-not (Test-Path $TargetFile)) {
    Write-Host "Downloading tla2tools.jar $Version"
    Invoke-WebRequest -Uri $Url -OutFile "$TargetFile.tmp"
    Move-Item -Force "$TargetFile.tmp" $TargetFile
} else {
    Write-Host "tla2tools.jar already present."
}
