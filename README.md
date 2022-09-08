# Manga/Light Novel ISBN Metadata Puller
An automation script that takes cbz manga and epub light novel files, searches them up on google-books, kobo books, barnes & noble, or bookwalker, validates the metadata and writes to the file. Writing for manga is done with comictagger, and writing for light novels is done with calibre.

The script is currently use at your own risk. It is not currently user friendly. I need to clean up some code, do a more proper readme with all the available options, and cleanup/fix the requirements. Give me some time.

Currently requires extracted covers alongside the .cbz and .epub files. You can provide your own or use https://github.com/zachstultz/komga-cover-extractor, I will add support for loading them from within the file itself, thus elimating this requirement.
