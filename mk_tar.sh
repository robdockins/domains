#!/bin/sh
mkdir -p domains
grep '\.v' Make | xargs -I '{}' cp '{}' domains/
cp -r html domains/ || echo "no html"
cp LICENSE README Make Makefile domains/
tar cfz domains.tar.gz domains/
rm -r domains
