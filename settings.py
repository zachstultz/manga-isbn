# Prompt user before metadata is written to the file
manualmetadata = False

# Skips updating metadata to the file
skip_updating_metadata = False

# Prompts the user before the zip comment is written
manual_zip_comment_approval = False

# If the update itself is incredibly similar to the original
# it will be auto-approved
#
# EX: Minor punctuation changes in a volume's description
manual_meta_similarity_skip = False

# Print the extracted text that the ISBN came from alongside the result
print_extracted_texts_with_result = False

# Write metadata to the file automatically
write_metadata_to_file = True

# Match API via image comparison
only_image_comparision = False

# Skip Google API search + image comparison
skip_image_comparison = False

# Sleep at certain intervals to avoid API rate limiting
api_rate_limit = True

# Apply multi-processing when processing image links
multi_process_image_links = False

# Skip letters A-#
skip_letters = False

# Allowed directory letters (skip directly to M-Z dirs within the root)
accepted_letters = ""

# Skip the current file if an ISBN is found within the zip comment
skip_file_if_isbn_in_zip_comment = False

# Skip the current file if a zip comment is found
skip_if_has_zip_comment = False

# Skip files containing metadata
skip_if_has_metadata = False

# Skip all files that were not tagged by comictagger
skip_all_non_comic_tagger_tagged = False

# Square Enix releases are not released digitally on Google Books. Paperback metadata will be used.
square_enix_bypass = True

# Scrape Google
scrape_google = True

# Scrape Kobo Books
scrape_kobo = True

# Scrape Bookwalker
scrape_bookwalker = True

# Scrape Barnes and Noble
scrape_barnes_and_noble = True

# Scrape Comic Vine
scrape_comic_vine = False

# Comic Vine API Key
comic_vine_api_key = ""

# Google Books API Key
google_books_api_key = ""

# Skip non-volume ones
skip_non_volume_ones = False

# Ignored folder names
ignored_folder_names = []

# Log to various files for various reasons
log_to_file = True

# Skip volumes that are older than the set time in minutes
skip_volumes_older_than_x_time = False

# Skip any volume comment that already contains an Anilist ID
skip_volume_if_already_has_anilist_id = False

# Skip any volume coment that already contains a Volume ID
skip_volume_if_already_has_volume_id = False

# Skip any volume comment that already contains a Series ID
skip_volume_if_already_has_series_id = False

# True = image similarity uses internal file cover, False = image similarity uses external file cover
use_internal_cover = False

# Skip any files that were tagged by Google Books
skip_google_metadata = False

# Only update if new title
only_update_if_new_title = False

# Allow both digital and paperback results to be accepted (not recommended)
allow_non_is_ebook_results = False

# Chapter support is currently experimental and may not work as intended
chapter_support_toggle = True

# Skip volumes that are labeled "volume 1"
skip_volume_one = False

# Skip items that have a web link in comicinfo.xml
skip_web_link = False

# Only update if new title
only_update_if_new_title = False

# Will skip every file until it gets to the passed in one.
skip_to_file = ""

# Will skip every directory until it gets to the passed in one.
skip_to_directory = ""

# Skips any cbz volume that doesn't contain a digital keyword
skip_non_digital_manga = True

# Mutes settings output
mute_settings_output = False

# Asks the user to submit a series_id for scraping
manual_series_id_mode = False
