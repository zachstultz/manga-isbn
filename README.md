# Manga/Light Novel ISBN Metadata Puller
An automation script that takes cbz manga and epub light novel files, searches them up on google-books, kobo books, barnes & noble, or bookwalker, validates the metadata and writes to the file. Writing for manga is done with comictagger, and writing for light novels is done with calibre.

# Docker
```
docker run -d \
    --name manga_isbn \
    -e TZ=Etc/UTC \
    -e PUID=1000 \
    -e PGID=1000 \
    -e FILE=<file_value> \
    -e FOLDER_PATH=<path_value> \
    -e MANUAL_METADATA=<manualmetadata_value> \
    -e SKIP_COMIC_INFO=<skip_comic_info_value> \
    -e SKIP_LETTERS=<skip_letters_value> \
    -e ONLY_IMAGE_COMPARISION=<only_image_comparision_value> \
    -e SKIP_ALL_NON_COMIC_TAGGER_TAGGED=<skip_all_non_comic_tagger_tagged_value> \
    -e SKIP_FILE_IF_ISBN_IN_ZIP_COMMENT=<skip_file_if_isbn_in_zip_comment_value> \
    -e SKIP_IF_HAS_ZIP_COMMENT=<skip_if_has_zip_comment> \
    -e ACCEPTED_FILE_TYPES=<accepted_file_types_value> \
    -e WEBHOOK=<webhook_value> \
    -e SKIP_NOVELS_WITH_METADATA=<skip_novels_with_metadata_value> \
    -e SKIP_NON_VOLUME_ONES=<skip_non_volume_ones_value> \
    -e SKIP_VOLUMES_OLDER_THAN_X_TIME=<skip_volumes_older_than_x_time_value> \
    -e SCRAPE_GOOGLE=<scrape_google_value> \
    -e SCRAPE_BOOKWALKER=<scrape_bookwalker_value> \
    -e SCRAPE_KOBO=<scrape_kobo_value> \
    -e SKIP_VOLUME_IF_ALREADY_HAS_ANILIST_ID=<skip_volume_if_already_has_anilist_id_value> \
    -e SCRAPE_BARNES_AND_NOBLE=<scrape_barnes_and_noble_value> \
    -e SCRAPE_COMIC_VINE=<scrape_comic_vine_value> \
    -e SKIP_GOOGLE_METADATA=<skip_google_metadata_value> \
    -e SORT=<sort_value> \
    -e USE_INTERNAL_COVER=<use_internal_cover_value> \
    -e SKIP_VOLUME_ONE=<skip_volume_one_value> \
    -e SKIP_WEB_LINK=<skip_web_link_value> \
    -e ONLY_UPDATE_IF_NEW_TITLE=<only_update_if_new_title_value> \
    -e SKIP_TO_FILE=<skip_to_file_value> \
    -e SKIP_TO_DIRECTORY=<skip_to_directory_value> \
    -e SKIP_NON_DIGITAL_MANGA=<skip_non_digital_manga> \
    -e MANUAL_ZIP_COMMENT_APPROVAL=<manual_zip_comment_approval> \
    -v /path/to/path/or/file:/path/to/path/or/file \
    -v /data/docker/manga_isbn/logs:/app/logs \
    -v /path/to/custom/settings.py:/app/settings.py:ro \ # optional, overrides default
    zachstultz/manga_isbn:master
```
