#!/bin/sh
#
# Terrible Bourne shell script wrapper around `tar vxf`, that ensures
# that that a single directory is created from the archive.  That is,
# this script prevents tarbombs.
#
# Usage:
#  `x file`
#
# If `file` extracts to a single file or directory, no special action
# will be taken.  Otherwise, a single directory with the same name as
# `file`, with extension stripped, will be created and `file`
# extracted therein.
#
# This script requires a GNU-compatible userland (mostly for `tar` and
# `sed`).

set -e

if [ $# -lt 1 ]; then
    echo usage: x file
    exit 1
elif [ ! -f $1 ]; then
    echo file $1 does not exist
    exit 1
fi

# This multifile check is so gross and yet hilarious.
if [ $(tar tf "$1"|sed 's/\/.*//g'|sort -u|wc -l) -gt 1 ]; then
    dir=$(echo $1|sed 's/\(.tar.*\|.[^.]*\)$//')
    echo extracting to $dir
    mkdir $dir
    tar vxf "$1" -C $dir
else
    tar vxf "$1"
fi
