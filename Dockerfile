# Use a specific version of the Python image
FROM python:3.11.4-slim-bullseye

# Set the working directory to /app
WORKDIR /app

# Create a new user called "appuser"
RUN useradd -m appuser
ARG PUID=1000
ARG PGID=1000

# Set ownership to appuser and switch to "appuser"
# RUN echo "deb http://deb.debian.org/debian buster non-free" >> /etc/apt/sources.list
RUN apt-get update
RUN groupmod -o -g "$PGID" appuser && usermod -o -u "$PUID" appuser

# Allow users to specify UMASK (default value is 022)
ENV UMASK 022
RUN umask "$UMASK"

# Copy the current directory contents into the container at /app
COPY --chown=appuser:appuser . .

# Install Misc Stuff
RUN apt-get install -y tzdata nano

# Install necessary packages and requirements
RUN apt-get update
RUN apt-get install -y wget
RUN apt-get install -y build-essential
RUN apt-get install -y xdg-utils xz-utils libopengl0 libegl1
RUN wget -nv -O- https://download.calibre-ebook.com/linux-installer.sh | sh /dev/stdin
RUN apt-get install -y libicu-dev pkg-config python3-icu
RUN apt-get install -y /app/chrome/google-chrome-stable_current_amd64.deb
RUN apt-get install -y python3-pyqt5
RUN apt-get -y install tesseract-ocr
RUN pip3 install --no-cache-dir -r /app/requirements.txt
RUN pip3 install /app/python-anilist-1.0.9/.

# Cleanup
RUN apt-get autoremove -y
RUN rm -rf /var/lib/apt/lists/*

# Switch to "appuser"
USER appuser

# Set the default CMD arguments for the script
# --webhook is the only item using nargs that needs to be accounted for, and tested
CMD python3 -u manga_isbn.py \
    --file="$FILE" \
    --path="$FOLDER_PATH" \
    --manualmetadata="$MANUAL_METADATA" \
    --skip_comic_info="$SKIP_COMIC_INFO" \
    --skip_letters="$SKIP_LETTERS" \
    --only_image_comparision="$ONLY_IMAGE_COMPARISION" \
    --skip_all_non_comic_tagger_tagged="$SKIP_ALL_NON_COMIC_TAGGER_TAGGED" \
    --skip_file_if_isbn_in_zip_comment="$SKIP_FILE_IF_ISBN_IN_ZIP_COMMENT" \
    --skip_if_has_zip_comment="$SKIP_IF_HAS_ZIP_COMMENT" \
    --accepted_file_types="$ACCEPTED_FILE_TYPES" \
    --webhook="$WEBHOOK" \
    --skip_novels_with_metadata="$SKIP_NOVELS_WITH_METADATA" \
    --skip_non_volume_ones="$SKIP_NON_VOLUME_ONES" \
    --skip_volumes_older_than_x_time="$SKIP_VOLUMES_OLDER_THAN_X_TIME" \
    --scrape_google="$SCRAPE_GOOGLE" \
    --scrape_bookwalker="$SCRAPE_BOOKWALKER" \
    --scrape_kobo="$SCRAPE_KOBO" \
    --skip_volume_if_already_has_anilist_id="$SKIP_VOLUME_IF_ALREADY_HAS_ANILIST_ID" \
    --scrape_barnes_and_noble="$SCRAPE_BARNES_AND_NOBLE" \
    --scrape_comic_vine="$SCRAPE_COMIC_VINE" \
    --skip_google_metadata="$SKIP_GOOGLE_METADATA" \
    --sort="$SORT" \
    --use_internal_cover="$USE_INTERNAL_COVER" \
    --skip_volume_one="$SKIP_VOLUME_ONE" \
    --skip_web_link="$SKIP_WEB_LINK" \
    --only_update_if_new_title="$ONLY_UPDATE_IF_NEW_TITLE" \
    --skip_to_file="$SKIP_TO_FILE" \
    --skip_to_directory="$SKIP_TO_DIRECTORY" \
    --skip_non_digital_manga="$SKIP_NON_DIGITAL_MANGA" \
    --manual_zip_comment_approval="$MANUAL_ZIP_COMMENT_APPROVAL"