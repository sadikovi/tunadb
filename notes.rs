// open a database or create a new one
// - if directory does not exist -> new database, try to create it
// - if directory exists but does not have a marker file -> not a database directory, cannot open
// - if directory exists, has a marker file and no lock file -> existing database, open it
// - if directory exists, has a marker file, and has a lock file -> existing database, cannot open

/*

Page size is 4KB, 8KB, 16KB, 32KB, 64KB.
Page keys are integer, long, float, double, byte array.

0           1          4         8           12          16              20            22               24
+-----------+----------+---------+-----------+-----------+---------------+-------------+----------------+
| page type | reserved | page id | prev page | next page | overflow page | tuple count | free space ptr |
+-----------+----------+---------+-----------+-----------+---------------+-------------+----------------+
+-------------------------------+-------------------------------+---------------------------------------+
| slot 1 (2) | slot 2 (2) | ... | free space                    | key x value | key x value | ...       |
+-------------------------------+-------------------------------+---------------------------------------+
                                                 free space ptr ^

Page id always starts with 1. If page id is 0, it is treated as undefined.

Slot offset is 0 based, i.e. from the beginning of the page.
Slots are represented as u16 values encoded as bytes (little endian).

Keys and values are stored together (i.e. their binary representations are concatenated).

Fixed type is stored as bytes, e.g. 4 bytes for integer, 8 bytes for long.

Variable type (non-overflow) is stored as 2 bytes size + bytes.

Variable type (overflow) is stored as overflow bit + overflow page id + overflow page offset +
  4 bytes size + partial bytes (payload_size).

0           1               5                9
+-----------+---------------+----------------+
| page type | overflow page | free space ptr |
+-----------+---------------+----------------+
+--------------------------------------------+
| payload 1 | payload 2 | payload 3 | ...    |
+--------------------------------------------+

Overflow payload format:
- 2 bytes size + bytes
- overflow bit + overflow page id + overflow page offset + 2 bytes size + partial bytes

Given the page size and data type, we will calculate how many values we can store.
*/
