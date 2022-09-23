# Manga/Light Novel ISBN Metadata Puller
An automation script that takes cbz manga and epub light novel files, searches them up on google-books, kobo books, barnes & noble, or bookwalker, validates the metadata and writes to the file. Writing for manga is done with comictagger, and writing for light novels is done with calibre.

The script is currently use at your own risk. It is not currently user friendly. I need to clean up some code, do a more proper readme with all the available options, and cleanup/fix the requirements. Give me some time.

Currently can use either an external cover file with the same name as the cbz/epub file or it can find an internal one and use that for an image similarity match result. 

Parsing the internal isbn does not require this.
