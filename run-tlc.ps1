param(
    [string]$Module = "STLRepairAlgo",
    [string]$Config = "models/STLRepairAlgo.cfg"
)

.\scripts\bootstrap.ps1

java -cp tools/tla2tools.jar tlc2.TLC -config $Config "spec/$Module.tla"
