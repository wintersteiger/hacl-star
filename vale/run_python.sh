#!/bin/bash

set -e

PYTHON_MAJOR_MINOR=3.6

# Windows-only: print out the directory of the Python
windows_python_dir () {
  PYDIR=$(regtool -q get "/HKLM/Software/Python/PythonCore/$PYTHON_MAJOR_MINOR/InstallPath/" || true)
  if ! [[ -d $PYDIR ]] ; then
    PYDIR=$(regtool -q get "/HKCU/Software/Python/PythonCore/$PYTHON_MAJOR_MINOR/InstallPath/" || true)
  fi
  if ! [[ -d $PYDIR ]] ; then
    red "ERROR: Python $PYTHON_MAJOR_MINOR was not installed properly"
    exit 1
  fi
  echo "$PYDIR"
}

is_windows () {
  [[ $OS == "Windows_NT" ]]
}

if is_windows ; then
  pydir=$(windows_python_dir)
  echo $pydir
  "$pydir/python.exe" "$@"
else
  python$PYTHON_MAJOR_MINOR "$@"
fi
