#!/bin/bash
grep 'Clean (BE' backend.h | sed -e 's$Clean (\(BE[0-9a-zA-Z_]*\).*$/EXPORT: \1$' -e 's/$/\r/' > backend.link
grep 'Clean (BE' backend.h | sed -e 's$Clean (\(BE[0-9a-zA-Z_]*\).*$/EXPORT:\1$' -e 's/$/\r/' > backend.link64
grep 'Clean (BE' backend.h | sed -e 's/\Clean (\(BE[0-9a-zA-Z_]*\).*/\1/' -e 's/$/\r/' -e '1ibackend.dll\r' > backend_library
