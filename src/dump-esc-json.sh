#!/bin/sh

echo 'var EscapePackages = ['
go build -a -gcflags=-m=2 "$@" |& \
  sed -n '/^<escape>$/,/^<\/escape>$/p' | \
  sed 's/^<escape>$/,/' | \
  sed '/^<\/escape>$/d' |
  sed '1d'
echo '];'
