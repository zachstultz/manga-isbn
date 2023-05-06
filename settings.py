# Manual title extraction approval
manual_title_approval = False

# Prompt user before metadata is written to the file
manualmetadata = False

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

# Restrict the Google search to one or two searches
limit_google_search = False

# Apply multi-processing when processing image links
multi_process_image_links = False

# Process multiple CBZ/EPUB files at once
multi_process_files = False

# Apply multi-processing when pulling descriptions from a file list of EPUBs
multi_process_pulling_descriptions = True

# Multi-process the internal files of a file for an internal ISBN number
multi_process_internal_files_for_isbn_search = True

# Skip letters A-#
skip_letters = False

# Allowed directory letters (skip directly to M-Z dirs within the root)
accepted_letters = "[I-Z]"

# Skip the current file if an ISBN is found within the zip comment
skip_file_if_isbn_in_zip_comment = False

# Skip files containing comic information
skip_comic_info = False

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
scrape_comic_vine = True

# Comic Vine API Key
comic_vine_api_key = "73c30636bb53e8113ce54a6f7194ba94dd89e409"

# Skip non-volume ones
skip_non_volume_ones = False

# Amount of time to sleep when the API hits the rate limit in seconds
sleep_time = 35

# Amount of time to sleep when a limit is hit when web scraping
web_scrape_sleep_time = 5

# Amount of time to sleep between Comic Vine results
comic_vine_sleep_time = 36

# ISBN-13 regex used throughout the program
isbn_13_regex = "(9([-_. :]+)?7([-_. :]+)?(8|9)(([-_. :]+)?[0-9]){10})"

# Ignored folder names
ignored_folder_names = [
    "test",
    "Test",
    "Fairy Tail",
    "Gintama",
    "Can Someone Please Explain What's Going On",
    "Future Diary",
    "The Seven Deadly Sins",
]

# Total CBZ/EPUB files encountered
total_files = 0

# Files metadata was written to
items_changed = []

# Any errors encountered
errors = []

# Successful ISBN retrievals
successful_isbn_retrievals = []

# Unsuccessful ISBN retrievals
unsuccessful_isbn_retrievals = []

# Successful Google API matches
successful_api_matches = []

# Unsuccessful Google API matches
unsuccessful_api_matches = []

# EPUBs where we couldn't find an ISBN, but our second attempt was successful
# The second attempt being an OCR on all the
items_found_through_ocr_on_epub = []

# Items that failed an API match through string search and image comparison
items_not_found_through_image_comparision_search = []

# Amount of API hits for the current session
api_hits = 0

# Total amount of retries for an API request
total_api_re_attempts = 10

# Required image similarity score for image similarity
required_image_ssim_score = 0.74

# Required MSE score to indicate a good match
required_image_mse_score = 0.37

# Required string similarity score using similar method
required_similarity_score = 0.97

# Used when checking for a match to Anilist
sentence_similarity_score = 0.85

# Discord webhook URL for notifications about changes and errors
webhook = []

# Skip novels with a summary, aka skips novels that already have metadata
skip_novels_with_metadata = False

# Log to various files for various reasons
log_to_file = True

# Skip volumes that are older than the set time in minutes
skip_volumes_older_than_x_time = False

# Skip any volume comment that already contains an Anilist ID
skip_volume_if_already_has_anilist_id = False

# Translate title names to improve matching when matching to Anilist
translate_titles = False

# Cache for series ID results to avoid unnecessary API hits
series_ids_cache = []

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

# Cached Google Books results, for later use
cached_series_result = None

# Whether or not a successful match was made with the previous cached results
successful_match = False

# Cache for image links and their data
image_link_cache = []

# Skip volumes that are labeled "volume 1"
skip_volume_one = False

# Skip items that have a web link in comicinfo.xml
skip_web_link = False

# Only update if new title
only_update_if_new_title = False
