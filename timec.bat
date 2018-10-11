@echo off
@setlocal

set start=%time%

:: Runs your command
cmd /c %*

set end=%time%

echo %end% - %start%