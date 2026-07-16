#!/bin/sh
# Build both language sites and publish them to the gh-pages branch.
set -e
cd "$(dirname "$0")"

lake exe lectures-en --output _out/en
lake exe lectures-pt --output _out/pt

staging=$(mktemp -d)
trap 'rm -rf "$staging"' EXIT

cp -r site/. "$staging"/
cp -r _out/en/html-multi "$staging"/en
cp -r _out/pt/html-multi "$staging"/pt
touch "$staging"/.nojekyll

cd "$staging"
git init -q -b gh-pages
git add -A
git commit -q -m "Deploy site"
git push -f https://github.com/ChristianoBraga/formal-software-verification.git gh-pages
echo "Deployed to https://christianobraga.github.io/formal-software-verification/"
