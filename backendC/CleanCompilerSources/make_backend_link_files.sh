grep 'Clean (BE' backend.h | sed -e 's\Clean (\/EXPORT: \' -e 's/\(BE[0-9a-zA-Z_]*\).*/\1/' -e 's/$/\r/' > backend.link
grep 'Clean (BE' backend.h | sed -e 's\Clean (\/EXPORT:\'  -e 's/\(BE[0-9a-zA-Z_]*\).*/\1/' -e 's/$/\r/' > backend.link64
