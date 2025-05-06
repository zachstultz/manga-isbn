import argparse
import ast
import calendar
import concurrent.futures
import datetime
import difflib as dl
import html
import io
import json
import os
import random
import string
import subprocess
import sys
import threading
import time
import traceback
import urllib.request
import xml.etree.ElementTree as ET
import zipfile
from datetime import date, datetime
from difflib import SequenceMatcher
from functools import lru_cache, partial
from math import log10, sqrt
from urllib.parse import urlparse

import anilist
import base64
import cProfile
import cv2
import langcodes
import nltk
import numpy as np
import pytesseract
import regex as re
import requests
import scandir
import translators as ts
from bs4 import BeautifulSoup, SoupStrainer
from collections import defaultdict
from discord_webhook import DiscordEmbed, DiscordWebhook
from langcodes import *
from langdetect import detect
from lxml import etree
from nltk.tokenize import sent_tokenize
from PIL import Image
from selenium import webdriver
from selenium.webdriver.chrome.service import Service as ChromeService
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from settings import *
from simyan.comicvine import Comicvine, ComicvineResource
from simyan.sqlite_cache import SQLiteCache
from skimage.metrics import structural_similarity as ssim
from titlecase import titlecase
from unidecode import unidecode
from webdriver_manager.chrome import ChromeDriverManager

script_version = (1, 1, 41)
script_version_text = "v{}.{}.{}".format(*script_version)

# ======= REQUIRED INSTALLS =======
# 1. WGET Install: sudo apt-get install wget -y
# 2. Calibre Install: sudo apt-get install xdg-utils libxcb-cursor0 libxcb-xinerama0 -y && sudo apt-get install xz-utils -y && sudo apt-get install libopengl0 -y && sudo apt-get install libegl1 -y && wget -nv -O- https://download.calibre-ebook.com/linux-installer.sh | sudo sh /dev/stdin
# 3. Misc (required for requirements & comictagger to install successfully): sudo apt-get install libicu-dev -y && sudo apt-get install pkg-config -y && sudo apt-get install python3-icu
# 4. Comictagger Install: sudo pip3 install comictagger
# 5. Chrome Install: sudo apt-get update && sudo apt install /scripts/komga-cover-extractor/addons/manga_isbn/chrome/google-chrome-stable_current_amd64.deb -y
# 6. PyQT5 Install: sudo apt-get install python3-pyqt5 -y
# 7. Tesseract Install: sudo apt-get install tesseract-ocr -y
# 8. Requirements Install: pip3 install -r /data/docker/scripts/komga-cover-extractor/addons/manga_isbn/requirements.txt
# 9. Anilist Install: pip3 install /scripts/komga-cover-extractor/addons/manga_isbn/python-anilist-1.0.9/.

# downoads required items for nltk.tokenize
nltk.download("punkt")
nltk.download("punkt_tab")

# The script's root directory
ROOT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)))

# Where logs are written to.
LOGS_DIR = os.path.join(ROOT_DIR, "logs")

# global folder_accessor
folder_accessor = None

# Stat-related variables
errors = []
items_changed = []

# Docker Status
in_docker = False

# Check if the instance is running in docker.
# If the ROOT_DIR is /app, then it's running in docker.
if ROOT_DIR == "/app":
    in_docker = True
    script_version_text += "-docker"

# Zip extensions
zip_extensions = [
    ".cbz",
    ".epub",
]

# Accepted file extensions for novels
novel_extensions = [".epub"]

# Accepted file extensions for manga
manga_extensions = [x for x in zip_extensions if x not in novel_extensions]

# All the accepted file extensions
file_extensions = novel_extensions + manga_extensions

# All the accepted image extensions
image_extensions = {".jpg", ".jpeg", ".png", ".tbn", ".webp"}

# The internal extenions that will be checked when looking for the isbn
# in an epub file.
internal_epub_extensions = ["xhtml", "opf", "ncx", "xml", "html"]

# Volume Regex Keywords to be used throughout the script
# ORDER IS IMPORTANT, if a single character volume keyword is checked first, then that can break
# cleaning of various bits of input.
volume_keywords = [
    "LN",
    "Light Novels?",
    "Novels?",
    "Books?",
    "Volumes?",
    "Vols?",
    "Discs?",
    "Tomo",
    "Tome",
    "Von",
    "V",
    "第",
    "T",
]

# Chapter Regex Keywords used throughout the script
chapter_keywords = [
    "Chapters?",
    "Chaps?",
    "Chs?",
    "Cs?",
    "D",
]

# Keywords to be avoided in a chapter regex.
# Helps avoid picking the wrong chapter number
# when no chapter keyword was used before it.
exclusion_keywords = [
    r"(\s)Part(\s)",
    r"(\s)Episode(\s)",
    r"(\s)Season(\s)",
    r"(\s)Arc(\s)",
    r"(\s)Prologue(\s)",
    r"(\s)Epilogue(\s)",
    r"(\s)Omake(\s)",
    r"(\s)Extra(\s)",
    r"(\s)- Special(\s)",
    r"(\s)Side Story(\s)",
    # r"(\s)S(\s)",
    r"(\s)Act(\s)",
    r"(\s)Special Episode(\s)",
    r"(\s)Ep(\s)",
    r"(\s)- Version(\s)",
    r"(\s)Ver(\s)",
    r"(\s)PT\.",
    r"(\s)PT(\s)",
    r",",
    r"(\s)×",
    r"\d\s*-\s*",
    r"\bNo.",
    r"\bNo.(\s)",
    r"\bBonus(\s)",
    r"(\]|\}|\)) -",
    r"\bZom(\s)",
    r"Tail -",
    r"꞉",
    r":",
    # r"\d\."
]

# Volume Regex Keywords to be used throughout the script
volume_regex_keywords = "(?<![A-Za-z])" + "|(?<![A-Za-z])".join(volume_keywords)

# Exclusion keywords joined by just |
exclusion_keywords_joined = "|".join(exclusion_keywords)

# Exclusion Regex Keywords to be used in the Chapter Regex Keywords to avoid incorrect number matches.
exclusion_keywords_joined_with_exclusion = "|".join(
    rf"(\s){keyword}(\s)" for keyword in exclusion_keywords
)

# Put the exclusion_keywords_joined_with_exclusion inside of (?<!%s)
exclusion_keywords_regex = r"(?<!%s)" % exclusion_keywords_joined_with_exclusion

# Chapter Regex Keywords to be used throughout the script
chapter_regex_keywords = r"(?<![A-Za-z])" + (r"|(?<![A-Za-z])").join(chapter_keywords)

### EXTENION REGEX ###
# File extensions regex to be used throughout the script
file_extensions_regex = "|".join(file_extensions).replace(".", r"\.")
# Manga extensions regex to be used throughout the script
manga_extensions_regex = "|".join(manga_extensions).replace(".", r"\.")
# Novel extensions regex to be used throughout the script
novel_extensions_regex = "|".join(novel_extensions).replace(".", r"\.")
# Image extensions regex to be used throughout the script
image_extensions_regex = "|".join(image_extensions).replace(".", r"\.")

# REMINDER: ORDER IS IMPORTANT, Top to bottom is the order it will be checked in.
# Once a match is found, it will stop checking the rest.
# IMPORTANT: Any change of order or swapping of regexes, requires change in full_chapter_match_attempt_allowed alternative logic!
chapter_searches = [
    r"\b\s-\s*(#)?(\d+)([-_.]\d+)*(x\d+)?\s*-\s",
    r"\b(?<![\[\(\{])(%s)(\.)?\s*(\d+)([-_.]\d+)*(x\d+)?\b(?<!\s(\d+)([-_.]\d+)*(x\d+)?\s.*)"
    % chapter_regex_keywords,
    r"(?<![A-Za-z]|%s)(?<![\[\(\{])(((%s)([-_. ]+)?(\d+)([-_.]\d+)*(x\d+)?)|\s+(\d+)(\.\d+)?(x\d+((\.\d+)+)?)?(\s+|#\d+|%s))"
    % (exclusion_keywords_joined, chapter_regex_keywords, manga_extensions_regex),
    r"((?<!^)\b(\.)?\s*(%s)(\d+)([-_.]\d+)*((x|#)(\d+)([-_.]\d+)*)*\b)((\s+-|:)\s+).*?(?=\s*[\(\[\{](\d{4}|Digital)[\)\]\}])"
    % exclusion_keywords_regex,
    r"(\b(%s)?(\.)?\s*((%s)(\d{1,2})|\d{3,})([-_.]\d+)*(x\d+)?(#\d+([-_.]\d+)*)?\b)\s*((\[[^\]]*\]|\([^\)]*\)|\{[^}]*\})|((?<!\w(\s))|(?<!\w))(%s)(?!\w))"
    % (chapter_regex_keywords, exclusion_keywords_regex, file_extensions_regex),
    r"^((#)?(\d+)([-_.]\d+)*((x|#)(\d+)([-_.]\d+)*)*)$",
]

# pre-compile the chapter_searches
chapter_search_patterns_comp = [
    re.compile(pattern, flags=re.IGNORECASE) for pattern in chapter_searches
]

subtitle_exclusion_keywords = [
    r"(?<!^)Volume",
    r"\b(vols?)(\b|\d+)",
    r"\b(?=.*(?:chap(?:ters?)?|ch(?:ap)?\.))(?=.*\d).*",
    r"\bedition\b",
    r"\bCollection\b",
    r"^\d+(\.\d+)?$",
    r"Manga Companion|The Manga|Light Novel",
]

# join with | to create a regex
subtitle_exclusion_keywords_regex = "|".join(subtitle_exclusion_keywords)

# Chrome driver location for selenium
chrome_driver_location = os.path.join(ROOT_DIR, "chrome/webdriver/chromedriver")

# To compress the extracted images
compress_image_option = False

# Whether to profile the script
profile_code = ""

# The path to the series_ids_cache.json file
cached_series_temp_path = "/tmp/series_ids_cache.json"

# Default image compression value.
# Pass in via cli
image_quality = 40

# Outputs the covers as WebP format
# instead of jpg format.
output_covers_as_webp = False

# Used to avoid duplicate titles
file_descriptions = []
result_subtitles = []


# argument parser
def image_arg_parser():
    parser = argparse.ArgumentParser(
        description="Extracts the ISBN number from an EPUB or does a Google API search with image-likeness > 70% and injects the metadata into the epub file."
    )
    parser.add_argument(
        "-f",
        "--file",
        help="The zip file to extract the image from",
        required=False,
    )
    parser.add_argument(
        "-p",
        "--path",
        help="The path to be recursively scanned for cbz and epub files.",
        required=False,
    )
    parser.add_argument(
        "-mmd",
        "--manualmetadata",
        help="If enabled, the user will be prompted before metadata is written to the file. Otherwise if False, data is written automatically",
        required=False,
    )
    parser.add_argument(
        "-sum",
        "--skip_updating_metadata",
        help="If enabled, the program will skip updating the metadata.",
        required=False,
    )
    parser.add_argument(
        "-sci",
        "--skip_comic_info",
        help="If enabled, the program will skip files that contain comic info inside the zip.",
        required=False,
    )
    parser.add_argument(
        "-sl",
        "--skip_letters",
        help="If enabled, the program will skip the letters A-#",
        required=False,
    )
    parser.add_argument(
        "-oic",
        "--only_image_comparision",
        help="If enabled, the program will only use image comparision to find a match",
        required=False,
    )
    parser.add_argument(
        "-sanctt",
        "--skip_all_non_comic_tagger_tagged",
        help="If enabled, the program will skip all files that were not tagged by comictagger.",
        required=False,
    )
    parser.add_argument(
        "-sfiiizc",
        "--skip_file_if_isbn_in_zip_comment",
        help="If enabled, the program will skip the current file if an isbn is found within the zip comment.",
        required=False,
    )
    parser.add_argument(
        "--skip_if_has_zip_comment",
        help="Skip files that have a zip comment.",
        required=False,
    )
    parser.add_argument(
        "-aft",
        "--accepted_file_types",
        help="The file types that the program will accept",
        required=False,
    )
    parser.add_argument(
        "-wh",
        "--webhook",
        action="append",
        nargs="*",
        help="The discord webhook url for notifications about changes and errors.",
        required=False,
    )
    parser.add_argument(
        "-snwm",
        "--skip_novels_with_metadata",
        help="If enabled, the program will skip novels that have a summary.",
        required=False,
    )
    parser.add_argument(
        "-snvo",
        "--skip_non_volume_ones",
        help="If enabled, the program will skip non-volume ones.",
        required=False,
    )
    parser.add_argument(
        "-twlv",
        "--skip_volumes_older_than_x_time",
        help="If enabled, the program will skip volumes that are older than x time.",
        required=False,
    )
    parser.add_argument(
        "-sg",
        "--scrape_google",
        help="If enabled, the program will scrape google for metadata",
        required=False,
    )
    parser.add_argument(
        "-sbw",
        "--scrape_bookwalker",
        help="If enabled, the program will scrape bookwalker for metadata.",
        required=False,
    )
    parser.add_argument(
        "-sk",
        "--scrape_kobo",
        help="If enabled, the program will scrape kobo books for metadata.",
        required=False,
    )
    parser.add_argument(
        "--skip_volume_if_already_has_anilist_id",
        help="If enabled, the program will skip volumes that already have an anilist id.",
        required=False,
    )
    parser.add_argument(
        "--skip_volume_if_already_has_volume_id",
        help="If enabled, the program will skip volumes that already have a series id.",
        required=False,
    )
    parser.add_argument(
        "--skip_volume_if_already_has_series_id",
        help="If enabled, the program will skip volumes that already have a series id.",
        required=False,
    )
    parser.add_argument(
        "-sban",
        "--scrape_barnes_and_noble",
        help="If enabled, the program will scrape barnes for metadata.",
        required=False,
    )
    parser.add_argument(
        "-scv",
        "--scrape_comic_vine",
        help="If enabled, the program will scrape comic_vine for metadata.",
        required=False,
    )
    parser.add_argument(
        "-sgm",
        "--skip_google_metadata",
        help="If enabled, the program will skip files that already have google metadata.",
        required=False,
    )
    parser.add_argument(
        "-s",
        "--sort",
        help="If enabled, the program will sort the files and folders alphabetically, useful when debugging, not reccomended for fastest file seek.",
        required=False,
    )
    parser.add_argument(
        "-uic",
        "--use_internal_cover",
        help="If enabled, the program will use the internal cover for image similarity.",
        required=False,
    )
    parser.add_argument(
        "-svo",
        "--skip_volume_one",
        help="If enabled, the program will skip volume ones.",
        required=False,
    )
    parser.add_argument(
        "-swl",
        "--skip_web_link",
        help="If enabled, the program will skip files that have a web link.",
        required=False,
    )
    parser.add_argument(
        "--only_update_if_new_title",
        help="If enabled, the program will only update the title if it is different.",
        required=False,
    )
    parser.add_argument(
        "--skip_to_file",
        help="If enabled, the program will skip every file until it gets to the passed in one.",
        required=False,
    )
    parser.add_argument(
        "--skip_to_directory",
        help="If enabled, the program will skip every directory until it gets to the passed in one.",
        required=False,
    )
    parser.add_argument(
        "--skip_non_digital_manga",
        help="If enabled, the program will skip any files that are not digital manga.",
        required=False,
    )
    parser.add_argument(
        "--manual_zip_comment_approval",
        help="If enabled, the program will ask for approval before writing the zip comment.",
        required=False,
    )
    parser.add_argument(
        "--mute_settings_output",
        help="If enabled, the program will not print the settings.",
        required=False,
    )
    parser.add_argument(
        "--manual_series_id_mode",
        help="If enabled, the program will ask the user to submit a series_id for scraping.",
        required=False,
    )
    return parser


class File:
    def __init__(
        self,
        name,
        extensionless_name,
        basename,
        extension,
        root,
        path,
        extensionless_path,
        volume_number,
        file_type,
        header_extension,
    ):
        self.name = name
        self.extensionless_name = extensionless_name
        self.basename = basename
        self.extension = extension
        self.root = root
        self.path = path
        self.extensionless_path = extensionless_path
        self.volume_number = volume_number
        self.file_type = file_type
        self.header_extension = header_extension


class Volume:
    def __init__(
        self,
        file_type,
        series_name,
        shortened_series_name,
        volume_year,
        volume_number,
        volume_part,
        index_number,
        release_group,
        name,
        extensionless_name,
        basename,
        extension,
        root,
        path,
        extensionless_path,
        extras,
        publisher,
        is_premium,
        subtitle,
        header_extension,
        multi_volume=None,
        is_one_shot=None,
    ):
        self.file_type = file_type
        self.series_name = series_name
        self.shortened_series_name = shortened_series_name
        self.volume_year = volume_year
        self.volume_number = volume_number
        self.volume_part = volume_part
        self.index_number = index_number
        self.release_group = release_group
        self.name = name
        self.extensionless_name = extensionless_name
        self.basename = basename
        self.extension = extension
        self.root = root
        self.path = path
        self.extensionless_path = extensionless_path
        self.extras = extras
        self.publisher = publisher
        self.is_premium = is_premium
        self.subtitle = subtitle
        self.header_extension = header_extension
        self.multi_volume = multi_volume
        self.is_one_shot = is_one_shot


# Class to store the book information
class Book:
    def __init__(
        self,
        isbn,
        title,
        series,
        number,
        volume,
        summary,
        published_date,
        year,
        month,
        day,
        writer,
        publisher,
        page_count,
        categories,
        language,
        preview_link,
        image_links,
        part,
        series_id,
        average_rating,
        is_ebook,
        api_link,
        maturity_rating,
        for_sale,
        provider,
        status,
        volume_count,
        genres=[],
        tags=[],
        series_id_order_number="",
        series_id_link="",
        google_volume_id="",
        subtitle="",
    ):
        self.isbn = isbn
        self.title = title
        self.series = series
        self.number = number
        self.volume = volume
        self.summary = summary
        self.published_date = published_date
        self.year = year
        self.month = month
        self.day = day
        self.writer = writer
        self.publisher = publisher
        self.page_count = page_count
        self.categories = categories
        self.language = language
        self.preview_link = preview_link
        self.image_links = image_links
        self.part = part
        self.series_id = series_id
        self.average_rating = average_rating
        self.is_ebook = is_ebook
        self.api_link = api_link
        self.maturity_rating = maturity_rating
        self.for_sale = for_sale
        self.provider = provider
        self.status = status
        self.volume_count = volume_count
        self.genres = genres
        self.tags = tags
        self.series_id_order_number = series_id_order_number
        self.series_id_link = series_id_link
        self.google_volume_id = google_volume_id
        self.subtitle = subtitle

    def to_dict(self):
        return {
            "isbn": self.isbn,
            "title": self.title,
            "series": self.series,
            "number": self.number,
            "volume": self.volume,
            "summary": self.summary,
            "published_date": self.published_date,
            "year": self.year,
            "month": self.month,
            "day": self.day,
            "writer": self.writer,
            "publisher": self.publisher,
            "page_count": self.page_count,
            "categories": self.categories,
            "language": self.language,
            "preview_link": self.preview_link,
            "image_links": self.image_links,
            "part": self.part,
            "series_id": self.series_id,
            "average_rating": self.average_rating,
            "is_ebook": self.is_ebook,
            "api_link": self.api_link,
            "maturity_rating": self.maturity_rating,
            "for_sale": self.for_sale,
            "provider": self.provider.to_dict(),  # Convert Provider object to dictionary
            "status": self.status,
            "volume_count": self.volume_count,
            "genres": self.genres,
            "tags": self.tags,
            "series_id_order_number": self.series_id_order_number,
            "series_id_link": self.series_id_link,
            "google_volume_id": self.google_volume_id,
            "subtitle": self.subtitle,
        }

    @classmethod
    def from_dict(cls, book_dict):
        # Convert provider dictionary to Provider object
        provider_dict = book_dict.pop("provider")
        provider = Provider.from_dict(provider_dict)

        # Merge provider object back into book dictionary
        book_dict["provider"] = provider

        return cls(**book_dict)


class Series_Page_Result:
    def __init__(self, series_id, series_name, results, api_results):
        self.series_id = series_id
        self.series_name = series_name
        self.results = results
        self.api_results = api_results

    def to_dict(self):
        return {
            "series_id": self.series_id,
            "series_name": self.series_name,
            "results": self.results,
            "api_results": [book.to_dict() for book in self.api_results],
        }

    @classmethod
    def from_dict(cls, result_dict):
        # Convert list of book dictionaries to list of Book objects
        api_results = [
            Book.from_dict(book_dict) for book_dict in result_dict["api_results"]
        ]

        # Merge book objects back into result dictionary
        result_dict["api_results"] = api_results

        return cls(**result_dict)


# Clas to store the result
class Result:
    def __init__(self, book, extracted_texts):
        self.book = book
        self.extracted_texts = extracted_texts


class Provider:
    def __init__(self, name, enabled, priority_number, icon_url):
        self.name = name
        self.enabled = enabled
        self.priority_number = priority_number
        self.icon_url = icon_url

    def to_dict(self):
        return {
            "name": self.name,
            "enabled": self.enabled,
            "priority_number": self.priority_number,
            "icon_url": self.icon_url,
        }

    @classmethod
    def from_dict(cls, provider_dict):
        return cls(**provider_dict)


# Holds our image link and image data for a cached array.
class ImageLinkCache:
    def __init__(self, image_link, image_data):
        self.image_link = image_link
        self.image_data = image_data


# our current list of supported metadata providers
providers = [
    Provider(
        "google-books",
        scrape_google,
        1,
        "https://upload.wikimedia.org/wikipedia/commons/thumb/5/53/Google_%22G%22_Logo.svg/1024px-Google_%22G%22_Logo.svg.png",
    ),
    Provider(
        "kobo",
        scrape_kobo,
        2,
        "https://upload.wikimedia.org/wikipedia/commons/thumb/6/6e/Rakuten_Kobo_Logo_2019.svg/1920px-Rakuten_Kobo_Logo_2019.svg.png",
    ),
    Provider(
        "barnes_and_noble",
        scrape_barnes_and_noble,
        3,
        "https://www.freepnglogos.com/uploads/barnes-and-noble-png-logo/dire-wolf-books-barnes-and-noble-png-logo-9.png",
    ),
    Provider(
        "bookwalker",
        scrape_bookwalker,
        4,
        "https://play-lh.googleusercontent.com/a7jUyjTxWrl_Kl1FkUSv2FHsSu3Swucpem2UIFDRbA1fmt5ywKBf-gcwe6_zalOqIR7V=w240-h480-rw",
    ),
    Provider(
        "comic_vine",
        scrape_comic_vine,
        5,
        "https://comicvine.gamespot.com/a/bundles/comicvinesite/images/logo.png",
    ),
]

provider_names = [provider.name for provider in providers]

cached_provider = Provider(
    "cached_series_id_results",
    True,
    1,
    "https://upload.wikimedia.org/wikipedia/commons/thumb/5/53/Google_%22G%22_Logo.svg/1024px-Google_%22G%22_Logo.svg.png",
)

# order providers by priority, lowest number first
providers.sort(key=lambda x: x.priority_number)


# Sends a message, prints it, and writes it to a file.
def send_message(
    message,
    discord=True,
    error=False,
    log=log_to_file,
    error_file_name="errors.txt",
    changes_file_name="changes.txt",
):
    print(message)
    if discord:
        send_discord_message(message)
    if error:
        errors.append(message)
        if log:
            write_to_file(error_file_name, message)
    else:
        items_changed.append(message)
        if log:
            write_to_file(changes_file_name, message)


last_hook_index = None


# Sends a discord message using the users webhook url
def send_discord_message(
    message,
    title=None,
    url=None,
    rate_limit=True,
    color=None,
    proxies={},
    fields=[],
    timestamp=True,
    author=None,
    image_url=None,
    thumbnail_url=None,
    image_local=None,
    thumbnail_local=None,
):
    hook = None
    global discord_webhook_url
    global last_hook_index
    global script_version

    if discord_webhook_url:
        if not last_hook_index and last_hook_index != 0:
            hook = discord_webhook_url[0]
        else:
            if last_hook_index == len(discord_webhook_url) - 1:
                hook = discord_webhook_url[0]
            else:
                hook = discord_webhook_url[last_hook_index + 1]
    if hook:
        last_hook_index = discord_webhook_url.index(hook)

    webhook = DiscordWebhook(url=None)
    embed = None
    try:
        if hook:
            if color and not embed:
                embed = DiscordEmbed()
                embed.color = color
            elif color and embed:
                embed.color = color
            if title and not embed:
                embed = DiscordEmbed()
                # Embed title is limited to 256 characters
                if len(title) > 256:
                    title = f"{title[:253]}..."
                embed.title = title
            elif title and embed:
                # Embed title is limited to 256 characters
                if len(title) > 256:
                    title = f"{title[:253]}..."
                embed.title = title
            if message and not embed:
                webhook.content = message
            elif message and embed:
                embed.description = message
            webhook.url = hook
            if rate_limit:
                webhook.rate_limit_retry = rate_limit
            if embed:
                if image_url and not image_local:
                    embed.set_image(url=image_url)
                elif image_local and not thumbnail_local:
                    webhook.add_file(file=image_local, filename="cover.jpg")
                    embed.set_image(url="attachment://cover.jpg")
                    embed.set_thumbnail(url="attachment://cover.jpg")
                if thumbnail_url and not thumbnail_local:
                    embed.set_thumbnail(url=thumbnail_url)
                if fields:
                    # An embed can contain a maximum of 25 fields
                    if len(fields) > 25:
                        fields = fields[:25]
                    for field in fields:
                        # A field name/title is limited to 256 character and the value of the field is limited to 1024 characters
                        if len(field["name"]) > 256:
                            field["name"] = f"{field['name'][:253]}..."
                        if len(field["value"]) > 1024:
                            field["value"] = f"{field['value'][:1021]}..."
                        embed.add_embed_field(
                            name=field["name"],
                            value=field["value"],
                            inline=field["inline"],
                        )
                if script_version_text:
                    embed.set_footer(text=script_version_text)
                if url:
                    embed.url = url
                if timestamp:
                    embed.set_timestamp()
                if author:
                    # Embed author name is limited to 256 characters
                    if len(author["name"]) > 256:
                        author["name"] = f"{author['name'][:253]}..."
                    embed.author = author
                webhook.add_embed(embed)
            if proxies:
                webhook.proxies = proxies
            response = webhook.execute()
        else:
            return
    except Exception as e:
        send_message(f"Failed to send discord message: {e}", error=True)


# execute command with subprocess and reutrn the output
def execute_command(command):
    try:
        process = subprocess.Popen(command, stdout=subprocess.PIPE)
        output, error = process.communicate()
        return output.decode("utf-8")
    except Exception as e:
        send_message(str(e), error=True)


# prints our ocr extracted texts
def print_extracted_texts(extracted_texts, separated=False):
    print(f"\n{'-'*80}\n{'Extracted Texts':^80}\n{'-'*80}")
    if separated:
        for text in extracted_texts:
            print(f"{text}\n{'-'*80}")
    else:
        print(f"{extracted_texts}\n{'-'*80}")


# Removes tuples from results
def remove_tuples_from_results(results):
    return [[t for t in result if t] for result in results]


# Searches for the isbn in a (KEYWORD) NUMBER
# or NUMBER (KEYWORD) format.
def find_all_searches(extracted_texts, file):
    # Highest priority first, ORDER IS IMPORTANT!
    keywords = [
        "EBOOK",
        "EPUB",
        "DIGITAL",
        "APP",
        "MOBI",
        "PDF",
        "PAPERBACK",
    ]
    # Define the regex pattern for keywords
    keywords_lined_regex = "(EBOOK|MOBI|EPUB|APP|PDF|PAPERBACK)"

    # Search for ISBN with keywords in the extracted texts
    results = re.findall(
        rf"({isbn_13_regex}([-_. :]|)+(\(?{keywords_lined_regex}\)?)|(\(?{keywords_lined_regex}\)?)([-_. :]|)+{isbn_13_regex})",
        extracted_texts,
        flags=re.IGNORECASE,
    )

    if results:
        results = remove_tuples_from_results(results)
        for keyword in keywords:
            for result in results:
                for text in result:
                    if re.search(
                        rf"({isbn_13_regex}([-_. :]|)+(\(?({keyword})\)?)|(\(?({keyword})\)?)([-_. :]|)+{isbn_13_regex})",
                        text,
                        flags=re.IGNORECASE,
                    ):
                        # Extract the ISBN from the text
                        text = re.sub(r"[^0-9]+", "", text, flags=re.IGNORECASE).strip()
                        print(f"\tFound ISBN: {text}")
                        print("\t\tChecking for google api result...\n")
                        # Check for Google API result
                        result = search_google_books(text, file)
                        if result:
                            return result
    return None


# Return the zip comment for the passed zip file
def get_zip_comment(zip_file):
    comment = ""
    try:
        with zipfile.ZipFile(zip_file, "r") as zip_ref:
            if zip_ref.comment:
                comment = zip_ref.comment.decode("utf-8")
    except Exception as e:
        send_message(
            f"\tFailed to get zip comment for: {zip_file} - Error: {e}", error=True
        )
    return comment


# Write the passed string to the zip file's comment
def write_zip_comment(zip_file, comment):
    # Write the comment to the zip file
    with zipfile.ZipFile(zip_file, "a") as zip_ref:
        zip_ref.comment = comment.encode("utf-8")

    # Verify that the comment was written
    if get_zip_comment(zip_file) != comment:
        return False
    return True


# Prints our results for the user
def print_book_result(result, anilist=False):
    try:
        discord_message_fields = []

        # Assign the book variable based on the available attribute
        book = result.book if hasattr(result, "book") else result

        # If there is book information
        if book:
            item_type = "Book" if not anilist else "AniList"
            print(f"\n{'-'*30}[{item_type} Information]{'-'*30}")

            # Get a list of all non-callable and non-system attributes from the book object
            attributes = [
                attr
                for attr in dir(book)
                if not callable(getattr(book, attr)) and not attr.startswith("__")
            ]

            # Iterate through attributes and print their values
            for attr in attributes:
                value = getattr(book, attr)

                # If the value isn't empty
                if value:
                    # Titlecase the attribute and remove underscores
                    capitalized = titlecase(replace_underscores(attr))

                    # If the attribute is a provider, get the provider's name
                    if capitalized.lower() == "provider":
                        value = book.provider.name if book.provider else "Unknown"

                    # Truncate value and attribute name if they exceed Discord's max lengths
                    value = (
                        f"{value[:1021]}..." if len(str(value)) > 1024 else str(value)
                    )
                    capitalized = (
                        f"{capitalized[:253]}..."
                        if len(capitalized) > 256
                        else capitalized
                    )

                    # Print the attribute and its value
                    message = convert_to_ascii(f"\t{capitalized}: {value}")
                    print(f"\t{message}")

                    # Add the attribute and value to the Discord message fields
                    discord_message_fields.append(
                        {
                            "name": capitalized,
                            "value": str(value),
                            "inline": False,
                        }
                    )

            # If there are Discord message fields
            if discord_message_fields:
                # Initialize variables
                image_data_to_use = None
                link_to_use = None
                image_to_use = "NONE"
                title_to_use = "NO TITLE"

                # Get image and title information from AniList, if available
                if anilist:
                    cover = result.cover
                    if cover:
                        if hasattr(cover, "extra_large"):
                            image_to_use = cover.extra_large
                        elif hasattr(cover, "large"):
                            image_to_use = cover.large
                        elif hasattr(cover, "medium"):
                            image_to_use = cover.medium
                        elif hasattr(cover, "small"):
                            image_to_use = cover.small

                    title = result.title
                    if title:
                        if hasattr(title, "english"):
                            title_to_use = title.english
                        elif hasattr(title, "romaji"):
                            title_to_use = title.romaji
                        elif hasattr(title, "native"):
                            title_to_use = title.native

                # Get image information from book's image links, if available
                if hasattr(book, "image_links") and book.image_links:
                    image_to_use = book.image_links[min(1, len(book.image_links) - 1)]

                # Check if the image is in the cache
                if image_to_use and image_link_cache:
                    for image in image_link_cache:
                        if image_to_use == image.image_link:
                            image_data_to_use = io.BytesIO(image.image_data)
                            break

                # Set up author information for the Discord message
                if not anilist:
                    author_info = {
                        "name": (
                            book.provider.name
                            if hasattr(book.provider, "name")
                            else "Unknown"
                        ),
                        "url": book.api_link if hasattr(book, "api_link") else "",
                        "icon_url": (
                            book.provider.icon_url
                            if hasattr(book.provider, "icon_url")
                            else ""
                        ),
                    }
                else:
                    author_info = {
                        "name": "AniList",
                        "url": result.url,
                        "icon_url": "https://upload.wikimedia.org/wikipedia/commons/thumb/6/61/AniList_logo.svg/512px-AniList_logo.svg.png",
                    }

                # Set up title information for the Discord message
                title_info = (
                    f"{book.series}: {book.title}"
                    if not anilist
                    else f"{title_to_use} ({result.id})"
                )

                # Set the URL for the Discord message
                link_to_use = book.api_link if not anilist else result.url

                # Send the Discord message with or without local image data, as appropriate
                if image_data_to_use:
                    # Send message with local image data
                    send_discord_message(
                        None,
                        title_info,
                        color=8421504,
                        fields=discord_message_fields,
                        url=link_to_use,
                        author=author_info,
                        image_local=image_data_to_use,
                    )
                else:
                    # Send message with image URL
                    send_discord_message(
                        None,
                        title_info,
                        color=8421504,
                        fields=discord_message_fields,
                        url=link_to_use,
                        author=author_info,
                        image_url=image_to_use,
                        thumbnail_url=image_to_use,
                    )

        if hasattr(result, "ssim_score") and getattr(result, "ssim_score"):
            print(f"\t\tSSIM Score: {result.ssim_score}")

            send_discord_message(
                None,
                "Image Similarity Score",
                color=8421504,
                fields=[
                    {
                        "name": f"SSIM >= {required_image_ssim_score}",
                        "value": str(result.ssim_score),
                        "inline": False,
                    },
                ],
            )

        print("-" * 80)

        # If extracted_texts attribute is available and not empty, print the extracted texts
        if (
            print_extracted_texts_with_result
            and hasattr(result, "extracted_texts")
            and result.extracted_texts
        ):
            print_extracted_texts(result.extracted_texts)
    except Exception as e:
        send_message(f"Failed to print book result: {e}", error=True)


# Remove all alphabetical characters from the input text and return the modified text.
@lru_cache(maxsize=None)
def remove_all_alphabetical_characters(text):
    return "".join([char for char in text if not char.isalpha()])


def search_for_text(text, file):
    find_all_result = find_all_searches(text, file)
    if find_all_result:
        return find_all_result

    result = text
    result = re.sub(r"(\/[0-9]{4}\/)", "", result, flags=re.IGNORECASE)
    result = re.sub(
        r"(\b([0-9]|[0-9][0-9])\.[A-Za-z]+)", "", result, flags=re.IGNORECASE
    )
    result = re.sub(
        r"([A-Za-z]+([0-9]|[0-9][0-9])\.(xhtml|html|css))",
        "",
        result,
        flags=re.IGNORECASE,
    )
    result = remove_all_alphabetical_characters(result)
    result = re.sub(r"[^0-9\s]", "", result)
    results = re.findall(rf"{isbn_13_regex}", result)
    results = remove_tuples_from_results(results)

    if results:
        for result in results:
            for t in result:
                t = re.sub(r"[^0-9]", "", t).strip()
                if len(t) == 13:
                    print(f"\tFound ISBN: {t}")
                    print("\t\tChecking google api result...\n")
                    api_result = search_google_books(t, file)
                    if api_result:
                        return api_result

    return None


# Searches the extracted text for the ISBN number
def isbn_search(text, file):
    # Search the entire text first
    all_search = search_for_text(text, file)
    if all_search:
        return all_search

    # Split text into lines and search each line individually
    lines = [line.strip() for line in text.split("\n") if line.strip()]
    for i, line in enumerate(lines):
        # Combine current and previous line (if not the first line)
        if i > 0:
            combined = f"{lines[i - 1]} {line}"
            combined_search = search_for_text(combined, file)
            if combined_search:
                return combined_search

        # Search individual line
        individual_search = search_for_text(line, file)
        if individual_search:
            return individual_search

    # ISBN not found
    return None


# Pre-compile the bracket pattern
brackets_pattern = re.compile(r"[(){}\[\]]")


# Determines if the string contains brackets
def contains_brackets(s):
    return bool(brackets_pattern.search(s))


# Retrieves the series name through various regexes
# Removes the volume number and anything to the right of it, and strips it.
@lru_cache(maxsize=None)
def get_series_name_from_volume(name, root=None, test_mode=False, second=False):
    # Remove starting brackets
    # EX: "[WN] Series Name" -> "Series Name"
    if starts_with_bracket(name) and re.search(
        r"^(\[[^\]]*\]|\([^\)]*\)|\{[^}]*\})+(\s+[A-Za-z]{2})", name
    ):
        # remove the brackets only
        name = re.sub(r"^(\[[^\]]*\]|\([^\)]*\)|\{[^}]*\})+\s+", "", name).strip()

    # replace _extra
    name = remove_dual_space(name.replace("_extra", ".5")).strip()

    # replace underscores
    name = replace_underscores(name) if "_" in name else name

    # remove brackets
    # name = remove_brackets(name) if contains_brackets(name) else name

    if root and is_one_shot(name, root, test_mode=test_mode):
        name = re.sub(
            r"([-_ ]+|)(((\[|\(|\{).*(\]|\)|\}))|LN)([-_. ]+|)(%s|).*"
            % file_extensions_regex.replace(r"\.", ""),
            "",
            name,
            flags=re.IGNORECASE,
        ).strip()
    else:
        if re.search(
            r"(\b|\s)(?<![A-Za-z])((\s|)-(\s|)|)(Part|)(\[|\(|\{)?(%s)(\.|)([-_. ]|)([0-9]+)(\b|\s).*"
            % volume_regex_keywords,
            name,
            flags=re.IGNORECASE,
        ):
            name = (
                re.sub(
                    r"(\b|\s)(?<![A-Za-z])((\s|)-(\s|)|)(Part|)(\[|\(|\{)?(%s)(\.|)([-_. ]|)([0-9]+)(\b|\s).*"
                    % volume_regex_keywords,
                    "",
                    name,
                    flags=re.IGNORECASE,
                )
            ).strip()
        else:
            name = re.sub(
                r"(\d+)?([-_. ]+)?((\[|\(|\})(.*)(\]|\)|\}))?([-_. ]+)?(%s)$"
                % file_extensions_regex,
                "",
                name,
                flags=re.IGNORECASE,
            ).strip()

    # Remove a trailing comma at the end of the name
    if name.endswith(","):
        name = name[:-1].strip()

    # remove the file extension if still remaining
    name = re.sub(r"(%s)$" % file_extensions_regex, "", name).strip()

    # Remove "- Complete" from the end
    # "Series Name - Complete" -> "Series Name"
    # EX File: Series Name - Complete v01 [Premium] [Publisher].epub
    if name.lower().endswith("complete"):
        name = re.sub(r"(-|:)\s*Complete$", "", name, flags=re.IGNORECASE).strip()

    return name


# regex out underscore from passed string and return it
@lru_cache(maxsize=None)
def replace_underscores(name):
    # Replace underscores that are preceded and followed by a number with a period
    name = re.sub(r"(?<=\d)_(?=\d)", ".", name)

    # Replace all other underscores with a space
    name = name.replace("_", " ")
    name = remove_dual_space(name).strip()

    return name


# Retrieves the series name from the file name and chapter number
def get_series_name_from_chapter(name, root, chapter_number="", second=False):
    # Remove starting brackets
    # EX: "[WN] Series Name" -> "Series Name"
    if starts_with_bracket(name) and re.search(
        r"^(\[[^\]]*\]|\([^\)]*\)|\{[^}]*\})+(\s+[A-Za-z]{2})", name
    ):
        # remove the brackets only
        name = re.sub(r"^(\[[^\]]*\]|\([^\)]*\)|\{[^}]*\})+\s+", "", name).strip()

    # Replace _extra
    name = name.replace("_extra", ".5")

    # Remove dual space
    name = remove_dual_space(name).strip()

    # remove the file extension
    name = get_extensionless_name(name)

    # replace underscores
    name = replace_underscores(name) if "_" in name else name

    regex_matched = False
    search = next(
        (r for pattern in chapter_search_patterns_comp if (r := pattern.search(name))),
        None,
    )

    if search:
        regex_matched = True
        search = search.group()
        name = name.split(search)[0].strip()

    result = ""

    if name:
        if isinstance(chapter_number, list):
            result = chapter_file_name_cleaning(
                name, chapter_number[0], regex_matched=regex_matched
            )
        else:
            result = chapter_file_name_cleaning(
                name, chapter_number, regex_matched=regex_matched
            )

    # Remove a trailing comma at the end of the name
    if result.endswith(","):
        result = result[:-1].strip()

    return result


# Cleans the chapter file name to get the series name
@lru_cache(maxsize=None)
def chapter_file_name_cleaning(
    file_name, chapter_number="", skip=False, regex_matched=False
):
    # removes any brackets and their contents
    file_name = (
        remove_brackets(file_name) if contains_brackets(file_name) else file_name
    )

    # Remove any single brackets at the end of the file_name
    # EX: "Death Note - Bonus Chapter (" -> "Death Note - Bonus Chapter"
    file_name = re.sub(r"(\s(([\(\[\{])|([\)\]\}])))$", "", file_name).strip()

    # EX: "006.3 - One Piece" -> "One Piece"
    if regex_matched != 2:
        file_name = re.sub(
            r"(^([0-9]+)(([-_.])([0-9]+)|)+(\s+)?([-_]+)(\s+))", "", file_name
        ).strip()

    # Remove number and dash at the end
    # EX: "Series Name 54 -" -> "Series Name"
    if regex_matched != 0 and file_name.endswith("-"):
        file_name = re.sub(
            r"(#)?([0-9]+)([-_.][0-9]+)*((x|#)([0-9]+)([-_.][0-9]+)*)*\s*-$",
            "",
            file_name,
        ).strip()

    # Remove - at the end of the file_name
    # EX: " One Piece -" -> "One Piece"
    if file_name.endswith("-"):
        file_name = re.sub(r"(?<![A-Za-z])(-\s*)$", "", file_name).strip()

    # Return if we have nothing but a digit left, if not skip
    if file_name.replace("#", "").isdigit() and not skip:
        return ""
    elif file_name.replace("#", "").replace(".", "", 1).isdigit() and not skip:
        return ""

    # if chapter_number and it's at the end of the file_name, remove it
    # EX: "One Piece 001" -> "One Piece"
    if not regex_matched:
        if chapter_number != "" and re.search(
            r"-?(\s+)?((?<!({})(\s+)?)(\s+)?\b#?((0+)?({}|{}))#?$)".format(
                chapter_regex_keywords,
                chapter_number,
                chapter_number,
            ),
            file_name,
        ):
            file_name = re.sub(
                r"-?(\s+)?((?<!({})(\s+)?)(\s+)?\b#?((0+)?({}|{}))#?$)".format(
                    chapter_regex_keywords,
                    chapter_number,
                    chapter_number,
                ),
                "",
                file_name,
            ).strip()

    # Remove any season keywords
    if "s" in file_name.lower() and re.search(
        r"(Season|Sea| S)(\s+)?([0-9]+)$", file_name, re.IGNORECASE
    ):
        file_name = re.sub(
            r"(Season|Sea| S)(\s+)?([0-9]+)$", "", file_name, flags=re.IGNORECASE
        )

    # Remove any subtitle
    # EX: "Series Name 179.1 - Epilogue 01 (2023) (Digital) (release_group).cbz"
    # "179.1 - Epilogue 01" -> "179.1"
    if ("-" in file_name or ":" in file_name) and re.search(
        r"(^\d+)", file_name.strip()
    ):
        file_name = re.sub(r"((\s+(-)|:)\s+).*$", "", file_name, re.IGNORECASE).strip()

    return file_name


# Determines if a volume file is a multi-volume file or not
# EX: TRUE == series_title v01-03.cbz
# EX: FALSE == series_title v01.cbz
@lru_cache(maxsize=None)
def check_for_multi_volume_file(file_name, chapter=False):
    # Set the list of keywords to search for
    keywords = volume_regex_keywords if not chapter else chapter_regex_keywords + "|"

    # Search for a multi-volume or multi-chapter pattern in the file name, ignoring any bracketed information in the name
    if "-" in file_name and re.search(
        # Use regular expressions to search for the pattern of multiple volumes or chapters
        r"(\b({})(\.)?(\s+)?([0-9]+(\.[0-9]+)?)([-]([0-9]+(\.[0-9]+)?))+\b)".format(
            keywords
        ),
        remove_brackets(file_name) if contains_brackets(file_name) else file_name,
        re.IGNORECASE,  # Ignore case when searching
    ):
        # If the pattern is found, return True
        return True
    else:
        # If the pattern is not found, return False
        return False


# Converts our list of numbers into an array of numbers, returning only the lowest and highest numbers in the list
# EX "1, 2, 3" -> [1, 3]
def get_min_and_max_numbers(string):
    # initialize an empty list to hold the numbers
    numbers = []

    # replace hyphens and underscores with spaces using regular expressions
    numbers_search = re.sub(r"[-_,]", " ", string)

    # remove any duplicate spaces
    numbers_search = remove_dual_space(numbers_search).strip()

    # split the resulting string into a list of individual strings
    numbers_search = numbers_search.split(" ")

    # convert each string in the list to either an integer or a float using the set_num_as_float_or_int function
    numbers_search = [set_num_as_float_or_int(num) for num in numbers_search if num]

    # if the resulting list is not empty, filter it further
    if numbers_search:
        # get lowest number in list
        lowest_number = min(numbers_search)

        # get highest number in list
        highest_number = max(numbers_search) if len(numbers_search) > 1 else None

        # discard any numbers in between the lowest and highest number
        numbers = [lowest_number]
        if highest_number:
            numbers.append(highest_number)

    # return the resulting list of numbers
    return numbers


def contains_non_numeric(input_string):
    try:
        # Try converting the string to a float
        float_value = float(input_string)

        # If successful, return False
        return False
    except ValueError:
        # If conversion to float fails, check if it's an integer
        return not input_string.isdigit()


# Pre-compiled chapter-keyword search for get_release_number()
chapter_number_search_pattern = re.compile(
    r"((%s)(\.)?(\s+)?(#)?(([0-9]+)(([-_.])([0-9]+)|)+))$" % exclusion_keywords_joined,
    flags=re.IGNORECASE,
)

# Pre-compiled volume-keyword search for get_release_number()
volume_number_search_pattern = re.compile(
    r"\b(?<![\[\(\{])(%s)((\.)|)(\s+)?([0-9]+)(([-_.])([0-9]+)|)+\b"
    % volume_regex_keywords,
    re.IGNORECASE,
)


# Finds the volume number and strips out everything except that number
@lru_cache(maxsize=None)
def get_release_number(file, chapter=False):

    # Cleans up the chapter's series name
    def clean_series_name(name):
        # Removes starting period
        # EX: "series_name. 031 (2023).cbz" -> "'. 031 (2023)"" -> "031 (2023)"
        if "." in name:
            name = re.sub(r"^\s*(\.)", "", name, re.IGNORECASE).strip()

        # Remove any subtitle
        # EX: "series_name 179.1 - Epilogue 01 (2023) (Digital) (release_group).cbz" ->
        # "" 179.1 - Epilogue 01"  -> "179.1"
        if ("-" in name or ":" in name) and re.search(r"(^\d+)", name.strip()):
            name = re.sub(r"((\s+(-)|:)\s+).*$", "", name, re.IGNORECASE).strip()

        # Removes # from the number
        # EX: #001 -> 001
        if "#" in name:
            name = re.sub(r"($#)", "", name, re.IGNORECASE).strip()

            # Removes # from bewteen the numbers
            # EX: 154#3 -> 154
            if re.search(r"(\d+#\d+)", name):
                name = re.sub(r"((#)([0-9]+)(([-_.])([0-9]+)|)+)", "", name).strip()

        # removes part from chapter number
        # EX: 053x1 or c053x1 -> 053 or c053
        if "x" in name:
            name = re.sub(r"(x[0-9]+)", "", name, re.IGNORECASE).strip()

        # removes the bracketed info from the end of the string, empty or not
        if contains_brackets(name):
            name = remove_brackets(name).strip()

        # Removes the - characters.extension from the end of the string, with
        # the dash and characters being optional
        # EX:  - prologue.extension or .extension
        name = re.sub(
            r"(((\s+)?-(\s+)?([A-Za-z]+))?(%s))" % file_extensions_regex,
            "",
            name,
            re.IGNORECASE,
        ).strip()

        if "-" in name:
            # - #404 - -> #404
            if name.startswith("- "):
                name = name[1:].strip()
            if name.endswith(" -"):
                name = name[:-1].strip()

        # remove # at the beginning of the string
        # EX: #001 -> 001
        if name.startswith("#"):
            name = name[1:].strip()

        return name

    results = []
    is_multi_volume = False
    keywords = volume_regex_keywords if not chapter else chapter_regex_keywords
    result = None

    # Replace _extra
    file = remove_dual_space(file.replace("_extra", ".5")).strip()

    # Replace underscores
    file = replace_underscores(file) if "_" in file else file

    is_multi_volume = (
        check_for_multi_volume_file(file, chapter=chapter) if "-" in file else False
    )

    if not chapter:  # Search for a volume number
        result = volume_number_search_pattern.search(file)
    else:  # Prep for a chapter search
        if has_multiple_numbers(file):
            extension_less_file = get_extensionless_name(file)

            if chapter_number_search_pattern.search(extension_less_file):
                file = chapter_number_search_pattern.sub("", extension_less_file)

                # remove - at the end of the string
                if file.endswith("-") and not re.search(
                    r"-(\s+)?(#)?([0-9]+)(([-_.])([0-9]+)|)+(x[0-9]+)?(\s+)?-", file
                ):
                    file = file[:-1].strip()

        # Search for a chapter match
        result = next(
            (
                r
                for pattern in chapter_search_patterns_comp
                if (r := pattern.search(file))
            ),
            None,
        )

    if result:
        try:
            file = result.group().strip() if hasattr(result, "group") else ""

            # Clean the series name
            if chapter:
                file = clean_series_name(file)

            # Remove volume/chapter keywords from the file name
            if contains_non_numeric(file):
                file = re.sub(
                    r"\b({})(\.|)([-_. ])?".format(keywords),
                    "",
                    file,
                    flags=re.IGNORECASE,
                ).strip()

                if contains_non_numeric(file) and re.search(
                    r"\b[0-9]+({})[0-9]+\b".format(keywords),
                    file,
                    re.IGNORECASE,
                ):
                    file = (
                        re.sub(
                            r"({})".format(keywords),
                            ".",
                            file,
                            flags=re.IGNORECASE,
                        )
                    ).strip()

            try:
                if is_multi_volume or (
                    ("-" in file or "_" in file)
                    and re.search(
                        r"([0-9]+(\.[0-9]+)?)([-_]([0-9]+(\.[0-9]+)?))+", file
                    )
                ):
                    if not is_multi_volume:
                        is_multi_volume = True

                    multi_numbers = get_min_and_max_numbers(file)
                    if multi_numbers:
                        results.extend(
                            (
                                int(volume_number)
                                if float(volume_number).is_integer()
                                else float(volume_number)
                            )
                            for volume_number in multi_numbers
                        )
                        if len(multi_numbers) == 1:
                            is_multi_volume = False
                            results = (
                                int(results[0])
                                if float(results[0]).is_integer()
                                else float(results[0])
                            )
                else:
                    # Remove trailing ".0" so conversion doesn't fail
                    if file.endswith("0") and ".0" in file:
                        file = file.split(".0")[0]
                    results = int(file) if float(file).is_integer() else float(file)

            except ValueError as v:
                send_message(f"Not a float: {file}: ERROR: {v}", error=True)
        except AttributeError:
            send_message(str(AttributeError.with_traceback), error=True)

    if results or results == 0:
        if is_multi_volume:
            return tuple(results)
        elif chapter:
            return results
        elif results < 2000:
            return results

    return ""


# Allows get_release_number() to use a cache
def get_release_number_cache(file, chapter=False):
    result = get_release_number(file, chapter=chapter)
    return list(result) if isinstance(result, tuple) else result


# get the title from the description
@lru_cache(maxsize=None)
def get_title_from_description(description):
    search = re.search(
        r"(^([\"\“]?[A-Z]+([0-9]+|[^A-Za-z0-9]+)([0-9]+)?)+)", description
    )

    if not search:
        return ""

    search = search.group().strip()

    # remove ending character or number preceded by a space
    search = re.sub(r"\s[A-Z]?[^A-Za-z0-9]?$", "", search).strip()

    # remove dual spaces
    search = remove_dual_space(search).strip()

    # remove start and end quotes
    search = re.sub(r"^[\"\“]|[\"\”]$", "", search).strip()

    # remove ending period
    search = re.sub(r"([A-Z])(\.$)", r"\1", search).strip()

    # remove any ending characters that have punctuation before them
    search = re.sub(r"(?<=[^\w\s,/])([A-Za-z])$", "", search).strip()

    if len(search) <= 3:
        return ""

    return search


volume_year_regex = r"(\(|\[|\{)(\d{4})(\)|\]|\})"


# Get the release year from the file metadata, if present, otherwise from the file name
def get_release_year(name, metadata=None):
    result = None

    match = re.search(volume_year_regex, name, re.IGNORECASE)
    if match:
        result = int(re.sub(r"(\(|\[|\{)|(\)|\]|\})", "", match.group()))

    if not result and metadata:
        release_year_from_file = None

        if "Summary" in metadata and "Year" in metadata:
            release_year_from_file = metadata["Year"]
        elif "dc:description" in metadata and "dc:date" in metadata:
            release_year_from_file = metadata["dc:date"].strip()
            release_year_from_file = re.search(r"\d{4}", release_year_from_file)
            release_year_from_file = (
                release_year_from_file.group() if release_year_from_file else None
            )

        if release_year_from_file and release_year_from_file.isdigit():
            result = int(release_year_from_file)
            if result < 1950:
                result = None

    return result


# Converts the passed volume_number into a float or an int.
def set_num_as_float_or_int(volume_number, silent=False):
    if volume_number == "":
        return ""

    try:
        if isinstance(volume_number, list):
            result = "-".join(
                [
                    (
                        str(int(float(num)))
                        if float(num) == int(float(num))
                        else str(float(num))
                    )
                    for num in volume_number
                ]
            )
            return result
        elif isinstance(volume_number, str) and "." in volume_number:
            volume_number = float(volume_number)
        else:
            if float(volume_number) == int(volume_number):
                volume_number = int(volume_number)
            else:
                volume_number = float(volume_number)
    except Exception as e:
        if not silent:
            send_message(
                f"Failed to convert volume number to float or int: {volume_number}\nERROR: {e}",
                error=True,
            )
            send_message(f"{e}", error=True)
        return ""
    return volume_number


# Removes hidden files
def remove_hidden_files(files):
    return [x for x in files if not x.startswith(".")]


# Removes any unaccepted file types
def remove_unaccepted_file_types(files, root, accepted_extensions, test_mode=False):
    return [
        file
        for file in files
        if get_file_extension(file) in accepted_extensions
        and (os.path.isfile(os.path.join(root, file)) or test_mode)
    ]


# Remove hidden folders from the list
def remove_hidden_folders(dirs):
    return [x for x in dirs if not x.startswith(".")]


# Determines if the string starts with a bracket
def starts_with_bracket(s):
    return s.startswith(("(", "[", "{"))


# Determines if the string ends with a bracket
def ends_with_bracket(s):
    return s.endswith((")", "]", "}"))


# check if volume file name is a chapter
@lru_cache(maxsize=None)
def contains_chapter_keywords(file_name):
    # Replace "_extra"
    file_name_clean = file_name.replace("_extra", ".5")

    # Replace underscores
    file_name_clean = (
        replace_underscores(file_name_clean).strip()
        if "_" in file_name_clean
        else file_name_clean
    )

    # Remove "c1fi7"
    file_name_clean = file_name_clean.replace("c1fi7", "")

    # Remove dual spaces
    file_name_clean = remove_dual_space(file_name_clean).strip()

    # Use compiled patterns for searching
    found = False
    for pattern in chapter_search_patterns_comp:
        result = pattern.search(file_name_clean)
        if result:
            result = result.group()
            if not (
                starts_with_bracket(result)
                and ends_with_bracket(result)
                and re.search(r"^((\(|\{|\[)\d{4}(\]|\}|\)))$", result)
            ):
                found = True
                break

    if not found and not contains_volume_keywords(file_name):
        # Remove volume year
        without_year = re.sub(volume_year_regex, "", file_name, flags=re.IGNORECASE)

        # Remove any 2000-2999 numbers at the end
        without_year = re.sub(r"\b(?:2\d{3})\b$", "", without_year, flags=re.IGNORECASE)

        # Check for chapter numbers
        chapter_numbers_found = re.search(
            r"(?<!^)(?<!\d\.)\b([0-9]+)(([-_.])([0-9]+)|)+(x[0-9]+)?(#([0-9]+)(([-_.])([0-9]+)|)+)?(\.\d+)?\b",
            without_year,
        )
        if chapter_numbers_found:
            found = True

    return found


volume_regex = re.compile(
    r"((\s?(\s-\s|)(Part|)+(?<![\[\(\{])(%s)(\.|)([-_. ]|)([0-9]+)\b)|\s?(\s-\s|)(Part|)(%s)(\.|)([-_. ]|)([0-9]+)([-_.])(\s-\s|)(Part|)(%s)([0-9]+)\s|\s?(\s-\s|)(Part|)(%s)(\.|)([-_. ]|)([0-9]+)([-_.])(\s-\s|)(Part|)(%s)([0-9]+)\s)"
    % (
        volume_regex_keywords,
        volume_regex_keywords,
        volume_regex_keywords,
        volume_regex_keywords,
        volume_regex_keywords,
    ),
    re.IGNORECASE,
)


# Checks if the passed string contains volume keywords
@lru_cache(maxsize=None)
def contains_volume_keywords(file):
    # Replace _extra
    file = file.replace("_extra", ".5")

    # Remove dual spaces
    file = remove_dual_space(file).strip()

    # Remove brackets
    clean_file = remove_brackets(file) if contains_brackets(file) else file

    # Replace underscores
    clean_file = (
        replace_underscores(clean_file).strip()
        if "_" in clean_file
        else clean_file.strip()
    )

    # Remove dual spaces
    clean_file = remove_dual_space(clean_file).strip()

    return bool(volume_regex.search(clean_file))


# Removes all chapter releases
def filter_non_chapters(files):
    return [
        file
        for file in files
        if not contains_chapter_keywords(file) or contains_volume_keywords(file)
    ]


# Trades out our regular files for file objects
def upgrade_to_volume_class(
    files,
    skip_release_year=False,
    skip_file_part=False,
    skip_multi_volume=False,
    test_mode=False,
):
    if not files:
        return []

    if test_mode:
        skip_release_year = True

    results = []
    for file in files:
        file_obj = Volume(
            file.file_type,
            file.basename,
            get_shortened_title(file.basename),
            (get_release_year(file.name) if not skip_release_year else None),
            file.volume_number,
            "",
            "",
            "",
            file.name,
            file.extensionless_name,
            file.basename,
            file.extension,
            file.root,
            file.path,
            file.extensionless_path,
            [],
            "",
            "",
            None,
            file.header_extension,
            (
                (
                    check_for_multi_volume_file(
                        file.name,
                        chapter=file.file_type == "chapter",
                    )
                )
                if not skip_multi_volume and "-" in file.name
                else False
            ),
            (
                is_one_shot(file.name, file.root, test_mode=test_mode)
                if file.file_type != "chapter"
                else False
            ),
        )

        if not skip_file_part:
            file_obj.volume_part = get_file_part(
                file_obj.name,
                series_name=file_obj.series_name,
                subtitle=file_obj.subtitle,
                chapter=file_obj.file_type == "chapter",
            )

        if file_obj.is_one_shot:
            file_obj.volume_number = 1

        if file_obj.volume_number != "":
            if (
                file_obj.volume_part != ""
                and not isinstance(file_obj.volume_number, list)
                and int(file_obj.volume_number) == file_obj.volume_number
            ):
                file_obj.index_number = file_obj.volume_number + (
                    file_obj.volume_part / 10
                )
            else:
                file_obj.index_number = file_obj.volume_number

        results.append(file_obj)
    return results


# Returns an extensionless name
def get_extensionless_name(file):
    return os.path.splitext(file)[0]


# Retrives the series name from matching the folder name and the file names
def get_series_name_from_contents(
    folder_name, file_names, required_matching_percent=100
):
    if not file_names:
        return ""

    min_matching_count = (
        required_matching_percent * len(file_names) / 100
    )  # Minimum number of file names to match
    series_name = ""

    for i, char in enumerate(folder_name):
        # Loop through characters of the folder name
        matching_count = sum(
            1
            for file_name in file_names
            if i < len(file_name) and file_name[i].lower() == char.lower()
        )
        if matching_count >= min_matching_count:
            series_name += char
        else:
            break

    # Check if series_name is at least three characters
    if len(series_name) < 3:
        series_name = ""

    return series_name.strip()


# Trades out our regular files for file objects
def upgrade_to_file_class(
    files,
    root,
    test_mode=False,
    clean=False,
):
    if not files:
        return []

    # Clean up the files array before usage
    if clean:
        files = clean_and_sort(
            root,
            files,
            test_mode=test_mode,
        )[0]

    # Create a list of tuples with arguments to pass to the File constructor
    file_types = [
        (
            "chapter"
            if not contains_volume_keywords(file) and contains_chapter_keywords(file)
            else "volume"
        )
        for file in files
    ]

    chapter_numbers = [
        get_release_number_cache(file, chapter=file_type == "chapter")
        for file, file_type in zip(files, file_types)
    ]

    file_args = [
        (
            file,
            get_extensionless_name(file),
            (
                get_series_name_from_chapter(file, root, chapter_number)
                if file_type == "chapter"
                else get_series_name_from_volume(file, root, test_mode=test_mode)
            )
            or get_series_name_from_contents(os.path.basename(root), [file]),
            get_file_extension(file),
            root,
            os.path.join(root, file),
            get_extensionless_name(os.path.join(root, file)),
            chapter_number,
            file_type,
            None,
        )
        for file, file_type, chapter_number in zip(files, file_types, chapter_numbers)
    ]

    results = [File(*args) for args in file_args]

    return results


# Cleans up the files array before usage
def clean_and_sort(
    root,
    files=[],
    dirs=[],
    sort=False,
    chapters=chapter_support_toggle,
    skip_remove_ignored_folders=False,
    skip_remove_hidden_files=False,
    skip_remove_unaccepted_file_types=False,
    skip_remove_hidden_folders=False,
    test_mode=False,
):
    # Remove ignored folder names if present
    if ignored_folder_names and not skip_remove_ignored_folders:
        ignored_parts = any(
            part for part in root.split(os.sep) if part in ignored_folder_names
        )
        if ignored_parts:
            return [], []

    # Sort files and directories
    if sort:
        files.sort()
        dirs.sort()

    # Process files
    if files:
        # Remove hidden files
        if not skip_remove_hidden_files:
            files = remove_hidden_files(files)

        # Remove unaccepted file types
        if not skip_remove_unaccepted_file_types and files:
            files = remove_unaccepted_file_types(
                files,
                root,
                file_extensions,
                test_mode=test_mode,
            )

        # Filter out all chapter releases
        if not chapters and files:
            files = filter_non_chapters(files)

    # Process directories
    if dirs:
        # Remove hidden folders
        if not skip_remove_hidden_folders:
            dirs = remove_hidden_folders(dirs)

        # Remove ignored folder names
        if not skip_remove_ignored_folders and dirs:
            dirs = remove_ignored_folders(dirs)

    return files, dirs


# Checks for any exception keywords that will prevent the chapter release from being deleted.
def check_for_exception_keywords(file_name, exception_keywords):
    pattern = "|".join(exception_keywords)
    return bool(re.search(pattern, file_name, re.IGNORECASE))


# Checks for volume keywords and chapter keywords.
# If neither are present, the volume is assumed to be a one-shot volume.
def is_one_shot(file_name, root=None, skip_folder_check=False, test_mode=False):
    files = []

    if test_mode:
        skip_folder_check = True

    if (
        contains_volume_keywords(file_name)
        or contains_chapter_keywords(file_name)
        or check_for_exception_keywords(file_name, exception_keywords)
    ):
        return False

    if not skip_folder_check:
        files = clean_and_sort(root, os.listdir(root))[0]

    if len(files) == 1 or skip_folder_check:
        return True

    return False


# Returns an extensionless name
def get_extensionless_name(file):
    return os.path.splitext(file)[0]


# only print the difference betwen the two strings
def print_diff(s1, s2):
    seq_matcher = dl.SequenceMatcher(None, s1, s2)
    print(f"\n\t{'-'*13}Summary Differences{'-'*13}")
    for tag, i1, i2, j1, j2 in seq_matcher.get_opcodes():
        print(
            f"\t\t{tag:7} s1[{i1}:{i2}] --> s2[{j1}:{j2}] {s1[i1:i2]!r:>6} --> {s2[j1:j2]!r}\n"
        )
    print(f"\t{'-'*47}")


# Converts an array of integers into a string containing each integer separated by a dash.
def convert_array_to_string_with_dashes(array):
    # Use a generator expression to convert each integer to a string, then join them with dashes
    return "-".join(str(num) for num in array)


# get identifiers from the passed zip comment
def get_identifiers(zip_comment):
    metadata = []

    if "identifiers" in zip_comment.lower():
        # split on Identifiers: and only keep the second half
        identifiers = ((zip_comment.split("Identifiers:")[1]).strip()).split(",")

        # remove any whitespace
        metadata = [x.strip() for x in identifiers]
    return metadata


def check_description_match(file_descriptions, extracted_title, series_name=None):
    if series_name and extracted_title in series_name:
        return True

    # Set remove punctuation
    rm_punct_table = str.maketrans("", "", string.punctuation)
    titles_only = [x.text for x in file_descriptions if x.type == "title"]

    if extracted_title in titles_only:
        return True

    titles_only = [
        remove_dual_space(unidecode(x.translate(rm_punct_table))).lower().strip()
        for x in titles_only
    ]

    # Remove punctuation from the extracted_title
    clean_extracted_title = extracted_title.translate(rm_punct_table)

    # Unidecode, remove dual spaces, and lowercase the extracted_title
    clean_extracted_title = (
        remove_dual_space(unidecode(clean_extracted_title)).lower().strip()
    )

    if clean_extracted_title in titles_only:
        return True

    # Attempt a comment match
    for desc in file_descriptions:
        if desc.type == "title":
            continue

        # Remove punctuation from the description
        clean_desc = desc.text.translate(rm_punct_table)

        # Unidecode, remove dual spaces, and lowercase the description and extracted_title
        clean_desc = remove_dual_space(unidecode(clean_desc)).lower().strip()

        if not clean_desc:
            continue

        try:
            if re.search(
                rf"^{clean_extracted_title}\b",
                clean_desc,
                re.IGNORECASE,
            ):
                return True
        except Exception as e:
            send_message(str(e), error=True)

    return False


# Looks up the IBSN number on Google Books API and returns the information
def search_google_books(
    isbn,
    file_name,
    text_search=None,
    max_results_num=15,
    in_line_search=False,
    number=None,
    volume_id=None,
    quoted_search=None,
    order_by=None,
    mute_output=False,
):
    global sleep_time
    global api_hits

    file_name = os.path.basename(file_name)
    base_api_link = ""
    text = ""

    try:
        # 1: Create the base api link
        if text_search:
            # 1.1: Add the search text if no volume_id is present
            if not volume_id:
                search_text = urllib.parse.quote(text_search)
                if not quoted_search:
                    base_api_link = (
                        "https://www.googleapis.com/books/v1/volumes?q=" + search_text
                    )
                else:
                    base_api_link = (
                        "https://www.googleapis.com/books/v1/volumes?q="
                        + '"'
                        + search_text
                        + '"'
                    )
            else:
                pass

            # 1.2: Add the search text with an intitle
            intitle_filter = ""
            if in_line_search:
                intitle_filter = get_search_keyword(
                    re.sub(
                        r"[^A-Za-z0-9\s]",
                        "",
                        remove_punctuation(
                            get_series_name_from_volume(
                                re.sub(r"[\-\_]", " ", file_name, flags=re.IGNORECASE)
                            )
                        ),
                    )
                )
            elif number:
                intitle_filter = (
                    f"{number[0]}" if isinstance(number, list) else f"{number}"
                )

            # 1.3: Add the intitle filter
            if intitle_filter:
                base_api_link += f"+intitle:{intitle_filter}"

            # 1.4: Set the result order
            if order_by:
                base_api_link += f"&orderBy={order_by}"

            # 1.5: Add the max results
            base_api_link += f"&maxResults={max_results_num}"

            # 1.6: Set the print type
            base_api_link += "&printType=books"

            # 1.7: Set the language restriction
            base_api_link += "&langRestrict=en"
        else:
            base_api_link = "https://www.googleapis.com/books/v1/volumes" + (
                f"/{volume_id}" if volume_id else f"?q=isbn:{isbn}"
            )

        if not mute_output:
            print(f"Search: {base_api_link}")

        # 2: Perform the api request
        with urllib.request.urlopen(base_api_link) as f:
            text = f.read()

        api_hits += 1

        # Check if we are close to the api rate limit
        if api_rate_limit and api_hits % 25 == 0:
            print(f"\n\tAPI Hits: {api_hits}")
            print(
                f"\tSleeping for {sleep_time} seconds to avoid being api-rate limited.\n"
            )
            time.sleep(sleep_time)

        # Return if we got no results
        if not text:
            return None

        decoded_text = text.decode("utf-8")
        obj = json.loads(decoded_text)

        # Return if we got no results
        if not obj:
            return None

        api_results = obj.get("items", []) if not volume_id else [obj] if obj else []

        books = []

        for item in api_results:
            subtitle = ""
            series_id_order_number = ""
            series_id_link = ""

            # Get the series id
            series_id = (
                item.get("volumeInfo", {}).get("seriesInfo", {}).get("volumeSeries", "")
            )

            # Get the series id order number
            if series_id:
                series_id = series_id[0].get("seriesId", "")
                series_id_link = (
                    f"https://play.google.com/store/books/series?id={series_id}"
                )
                series_id = f"series_id:{series_id}"
                series_id_order_number = set_num_as_float_or_int(
                    item.get("volumeInfo", {})
                    .get("seriesInfo", {})
                    .get("bookDisplayNumber", "")
                )

            # Get the is_ebook status
            is_ebook = (
                item.get("saleInfo", {}).get("isEbook", "")
                or item.get("accessInfo", {}).get("epub", {}).get("isAvailable", "")
                or series_id
            )

            # Get the saleability status
            for_sale = item.get("saleInfo", {}).get("saleability", "")

            # Set the file name to the title of the current api item
            if text_search or volume_id:
                isbn = 0
                file_name = (
                    item["volumeInfo"]["title"]
                    if "title" in item["volumeInfo"]
                    else file_name
                )

            # Get and set the file part
            part = get_file_part(file_name)

            # Convert the part to a float or int
            part = set_num_as_float_or_int(part) if part else ""

            id = item.get("id", "")
            volume_info = item["volumeInfo"]

            # Get the subtitle
            subtitle_search = item.get("volumeInfo", {}).get("subtitle", "")
            if subtitle_search:
                # Unidecode the subtitle
                subtitle = unidecode(subtitle_search)

                # Remove any volume keywords from the subtitle
                if re.search(
                    r"^(%s)(\s+)?(\.)?(\s+)?([0-9]+)(([-_.])([0-9]+)|)+((\s+(-)|:)\s+)"
                    % volume_regex_keywords,
                    subtitle.strip(),
                    re.IGNORECASE,
                ):
                    subtitle = re.sub(
                        r"^(%s)(\s+)?(\.)?(\s+)?([0-9]+)(([-_.])([0-9]+)|)+((\s+(-)|:)\s+)"
                        % volume_regex_keywords,
                        "",
                        subtitle.strip(),
                        re.IGNORECASE,
                    ).strip()

            # Get the maturity rating
            maturity_rating = volume_info.get("maturityRating", "")
            summary = volume_info.get("description", "")

            if summary:
                # Unicode the summary
                summary = unidecode(summary) if contains_unicode(summary) else summary

                # Unescape the summary
                summary = html.unescape(summary)

                # Remove all html tags from the summary
                # 'ANSWERS<br><br> What makes a Reaper?'
                if re.search(r"([a-z])(<br>)+([A-Z])", summary):
                    summary = re.sub(r"([a-z])(<br>)+([A-Z])", r"\1. \3", summary)
                if re.search(r"<[^>]*>", summary):
                    summary = re.sub(r"<[^>]*>", " ", summary)
                if re.search(r"(\s+)([\!\.\?])$", summary, re.IGNORECASE):
                    summary = re.sub(r"(\s+)([\!\.\?])$", r"\2", summary)

                # Remove any extra spaces
                summary = remove_dual_space(summary).strip()

                # Remove lone punctuation at the end of the summary
                # EX: `The story of Falcon.    !` --> `The story of Falcon.`
                if re.search(r"(\s+)([\.\!\?]$)", summary):
                    summary = re.sub(r"(\s+)([\.\!\?]$)", r"\2", summary).strip()

                # if summary has a period,exclamation, or questoin mark right next to a capital letter, put a space after the punctuation
                # EX: `The story of Falcon.A rift through time.` --> `The story of Falcon. A rift through time.`
                if re.search(r"([\.\!\?])([A-Z][a-zA-Z])", summary):
                    summary = re.sub(
                        r"([\.\!\?])\s*([A-Z]([a-zA-Z]))", r"\1 \2", summary
                    ).strip()

                # Combat . Between --> Combat. Between
                if re.search(r"([a-z])(\s+)([\.!?,])", summary):
                    summary = re.sub(r"([a-z])(\s+)([\.!?,])", r"\1\3", summary).strip()

                # " Accelerator --> "Accelerator
                if re.search(r"(\")(\s+)([A-Z])", summary):
                    summary = re.sub(r"(\")(\s+)([A-Z])", r"\1\3", summary)

                if re.search(r"([A-Z\.\!\?])(\")", summary) and not re.search(
                    r"(([A-Z\.\!\?])(\"))$", summary
                ):
                    summary = re.sub(r"([A-Z\.\!\?])(\")", r"\1 \2", summary)

                # Add a space between the title (all caps) and the summary_search
                summary = re.sub(
                    r"^([A-Z\s]{3,})([A-Z][a-z])", r"\1 \2", summary
                ).strip()

                # Remove any extra spaces
                summary = remove_dual_space(summary)

            # Get the volume number
            volume_number = get_release_number_cache(remove_brackets(file_name)) or (
                1 if is_one_shot(file_name, root) and not series_id_order_number else ""
            )

            # Reset the volume number if the series_id_order_number is different
            if (
                series_id_order_number
                and set_num_as_float_or_int(series_id_order_number) != volume_number
            ):
                volume_number = ""

            # Convert the volume number(s) to a float or int
            if volume_number != "":
                if isinstance(volume_number, list):
                    volume_number = [set_num_as_float_or_int(x) for x in volume_number]
                else:
                    volume_number = set_num_as_float_or_int(volume_number)

            # Get the ISBN number and set the api link
            api_link = ""

            if text_search or volume_id:
                identifiers = volume_info.get("industryIdentifiers", {})
                isbn = next(
                    (
                        identifier["identifier"]
                        for identifier in identifiers
                        if identifier["type"] == "ISBN_13"
                        or (
                            str(identifier["identifier"]).startswith("978")
                            and len(str(identifier["identifier"])) == 13
                        )
                    ),
                    "",
                )

            # Set the api link
            if volume_id or isbn:
                api_link = "https://www.googleapis.com/books/v1/volumes" + (
                    f"/{volume_id}" if volume_id else f"?q=isbn:{isbn}"
                )

            # Set the volume keyword for the title
            volume_keyword = "Volumes" if isinstance(volume_number, list) else "Volume"

            # Default title
            title = f"{volume_keyword} {convert_array_to_string_with_dashes(volume_number) if isinstance(volume_number, list) else volume_number}"
            if part:
                title += f" Part {part}"

            # Get the series name
            series = (
                get_series_name_from_volume(volume_info.get("title", ""))
                if text_search
                else get_series_name_from_volume(file_name)
            )

            # Get and set the title
            if "title" in volume_info and summary:
                extracted_title = get_title_from_description(summary)
                # Make sure we don't have a duplicate title
                if extracted_title:
                    # Set the title since no duplicate was found
                    title = titlecase(extracted_title)

            # Get the writer from authors
            writer = volume_info.get("authors", "")
            if writer and isinstance(writer, list):
                if len(writer) > 1:
                    combined = ""
                    for author in writer:
                        # Remove trailing punctuation: 'Tugikuru Corp.' --> 'Tugikuru Corp'
                        author = re.sub(r"[,.!?]", "", author).strip()

                        # Remove brackets: 'Tugikuru Corp (Test)' --> 'Tugikuru Corp'
                        author = re.sub(
                            r"((\s+)?([\(\{\[])(.*)([\]\}\)])(\s+)?)",
                            "",
                            author,
                        ).strip()

                        combined += f"{author}, " if author != writer[-1] else author
                    writer = combined
                else:
                    # Remove commas from the writer
                    writer = re.sub(r",", "", writer[0]).strip()

                # Titlecase the writer(s)
                writer = titlecase(writer)

            # Get the publisher
            publisher = volume_info.get("publisher", "")
            if publisher:
                # Unnecessary publisher information
                publisher = re.sub(
                    r"(,\s+|)?((LLC|Inc|\bCo\b).*)",
                    "",
                    publisher,
                    flags=re.IGNORECASE,
                ).strip()

                publisher = re.sub(r"[^a-zA-Z0-9\s-,\.]", "", publisher).strip()

                # Titlecase the publisher
                publisher = titlecase(publisher)

            year, month, day = "", "", ""
            published_date = volume_info.get("publishedDate", "")

            # Get the release date
            if published_date:
                year = published_date[0:4]
                month = published_date[5:7].zfill(2)
                day = published_date[8:10].zfill(2)

                published_date = f"{year}-{month}-{day}"
                published_date = published_date.rstrip("-")

            # Get the page count
            page_count = volume_info.get("pageCount", "")

            # Get the categories
            categories = volume_info.get("categories", [])

            # Get the language
            language = volume_info.get("language", "")

            # Standardize the language
            language = standardize_tag(language) if language else ""

            # Get the preview link
            preview_link = volume_info.get("previewLink", "")

            # Get the average rating
            average_rating = volume_info.get("averageRating", "")
            if average_rating:
                average_rating = set_num_as_float_or_int(average_rating)
                if average_rating > 5 and average_rating <= 10:
                    average_rating = average_rating / 2
                else:
                    average_rating = ""

            # Get the image links
            image_links = []
            image_links_search = volume_info.get("imageLinks", [])

            if image_links_search:
                for key, value in image_links_search.items():
                    # Stop after the first item
                    if image_links:
                        break

                    # Remove the thumbnail edge curl
                    thumbnail = re.sub(r"&edge=curl", "", value, flags=re.IGNORECASE)

                    # Incrase the size of the thumbnail to 800x1200
                    with_width_and_height_adjustment = f"{thumbnail}&fife=w800-h1200"

                    # Add the thumbnail to the image links
                    if with_width_and_height_adjustment not in image_links:
                        image_links.append(with_width_and_height_adjustment)

                    # Square Enix BYPASS
                    if (
                        "square" in publisher.lower() or "enix" in publisher.lower()
                    ) and thumbnail not in image_links:
                        image_links.append(thumbnail)

            # Default the ISBN (temp)
            if isbn == 0:
                isbn = ""

            # Default the API Link (temp)
            if not api_link:
                api_link = ""

            # Set the provider
            provider = next((x for x in providers if x.name == "google-books"), None)

            book = Book(
                isbn,
                title,
                series,
                volume_number,
                volume_number,
                summary,
                published_date,
                year,
                month,
                day,
                writer,
                publisher,
                page_count,
                categories,
                language,
                preview_link,
                image_links,
                part,
                series_id,
                average_rating,
                is_ebook,
                api_link,
                maturity_rating,
                for_sale,
                provider,
                status=None,
                volume_count=0,
                series_id_order_number=series_id_order_number,
                series_id_link=series_id_link,
                google_volume_id=id,
                subtitle=subtitle,
            )
            books.append(book)

        # Return the book(s)
        if not books:
            return None

        if len(books) > 1:
            return books[0] if not text_search else books
        else:
            return books[0]

    except Exception as e:
        send_message(str(e), error=True)
        return None


# Check the text file line by line for the passed message
def check_text_file_for_message(text_file, message):
    # Open the file in read mode using a context manager
    with open(text_file, "r") as f:
        # Check if any line in the file matches the message
        return any(line.strip() == message.strip() for line in f)


# Writes a log file
def write_to_file(
    file,
    message,
    without_timestamp=False,
    overwrite=False,
    check_for_dup=False,
    write_to=None,
    can_write_log=log_to_file,
):
    write_status = False
    logs_dir_loc = write_to or LOGS_DIR

    # check if the logs directory exists, if not create it
    if not os.path.exists(logs_dir_loc):
        try:
            os.makedirs(logs_dir_loc)
        except OSError as e:
            send_message(str(e), error=True)
            return False

    if can_write_log and logs_dir_loc:
        # get rid of formatting
        message = re.sub("\t|\n", "", str(message), flags=re.IGNORECASE).strip()
        contains = False

        # check if it already contains the message
        log_file_path = os.path.join(logs_dir_loc, file)

        if check_for_dup and os.path.isfile(log_file_path):
            contains = check_text_file_for_message(log_file_path, message)

        if not contains or overwrite:
            try:
                append_write = (
                    "a" if os.path.exists(log_file_path) and not overwrite else "w"
                )
                try:
                    now = datetime.now()
                    dt_string = now.strftime("%d/%m/%Y %H:%M:%S")

                    with open(log_file_path, append_write) as f:
                        if without_timestamp:
                            f.write(f"\n {message}")
                        else:
                            f.write(f"\n{dt_string} {message}")
                    write_status = True

                except Exception as e:
                    send_message(str(e), error=True, log=False)
            except Exception as e:
                send_message(str(e), error=True, log=False)
    return write_status


class InternalZipImage:
    def __init__(self, name, data):
        self.name = name
        self.data = data


# Parses the given ZIP file, extracting image files and returning them as InternalZipImage objects.
def parse_zip_file(zip_file):
    results = []
    try:
        # Open the ZIP file for reading
        with zipfile.ZipFile(zip_file, "r") as zip_ref:
            # Get a list of all files in the ZIP archive with image extensions
            images = [
                name
                for name in zip_ref.namelist()
                if get_file_extension(name) in image_extensions
            ]
            # Remove hidden files and sort the remaining files alphabetically
            images = remove_hidden_files(images)
            images.sort()
            if images:
                if len(images) > 17:
                    # Handle .cbz files differently
                    if zip_file.endswith(".cbz"):
                        # Get the last 17 images as back images
                        back_images = images[-17:]
                        # Get the first 7 images and reverse them as front images
                        front_images = images[:7][::-1]
                        # Combine the last 2 back images and the first 2 front images as the cover
                        comb = back_images[-2:][::-1] + front_images[:2]
                        # Add all remaining images that are not already in the cover to the final list
                        comb += [
                            img
                            for img in back_images + front_images
                            if img not in set(comb)
                        ]
                        images = comb
                    # Create a list of InternalZipImage objects from the image files
                results = [
                    InternalZipImage(image, zip_ref.read(image)) for image in images
                ]
    except Exception as e:
        # Handle any exceptions by sending an error message and writing the filename to a log file
        send_message(f"Error parsing ZIP file: {zip_file}, Error: {e}", error=True)
        write_to_file("bad_zip_file.txt", zip_file)
        return None
    # Return the list of InternalZipImage objects
    return results


# Extracts text from the given image using Tesseract OCR.
def extract_text_from_image(image):
    try:
        # Open the image from the bytes data and convert it to a numpy array
        starting_img = Image.open(io.BytesIO(image))
        starting_img = np.array(starting_img)
        # Use Tesseract to extract text from the image
        text = pytesseract.image_to_string(starting_img)
        return text
    except Exception as e:
        # Handle any exceptions by logging the error and sending an error message
        send_message(f"Text Extraction Failed: Error: {e}", error=True)
        write_to_file("isbn_script_errors.txt", str(e))
        return None


# Handles processing for a successfully matched book.
def process_book_match(book, zip_file, texts):
    result = None
    if book:
        isbn = ""
        if isinstance(book, list):
            isbn = book[0].isbn
            result = Result(book[0], texts)
        else:
            isbn = book.isbn
            result = Result(book, texts)

        message = f"\tSuccessful ISBN Match: https://www.googleapis.com/books/v1/volumes?q=isbn:{isbn}"
        send_message(f"{message}\n")
        message = f"{message} for File: {os.path.basename(zip_file)}"
        successful_api_matches.append(zip_file)
        write_to_file("success_api_match.txt", message)
    else:
        send_message(f"\tUnsuccessful API Match: {os.path.basename(zip_file)}")
        message = f"\tUnsuccessful API Match: {zip_file}"
        unsuccessful_api_matches.append(zip_file)
        write_to_file("\tFailed_api_match.txt", message)
    return result


# Search for and handle the retrieval of an ISBN number from an image.
def process_isbn_extraction(
    extracted_texts, image, zip_file, images, second=False, skip=False
):
    # search for the book using the extracted texts
    book = isbn_search(extracted_texts, zip_file)

    # check if the book has an ISBN
    if hasattr(book, "isbn") and book.isbn:
        # if an ISBN is found, log the success and return the book
        if not skip:
            send_message(f"\tISBN: {book.isbn} found in {os.path.basename(image)}")
        else:
            send_message(f"\tISBN: {book.isbn} found in file list.")
        successful_isbn_retrievals.append(zip_file)
        write_to_file(
            "success_isbn_retrievals.txt",
            f"\tISBN: {book.isbn} found in {os.path.basename(zip_file)}",
        )
        return book

    # if no ISBN is found and it's not the second pass, log the failure and return None
    elif not skip:
        print(f"\tNo ISBN found in {os.path.basename(image)}")
        if image == images[-1] and second:
            unsuccessful_isbn_retrievals.append(zip_file)
            write_to_file(
                "no_isbn.txt", f"\tNo ISBN found in {os.path.basename(zip_file)}"
            )
            return None


def process_zip_file_contents(zip_file, second_attempt=None):
    # Check if file exists
    if not os.path.isfile(zip_file):
        print("File does not exist")
        return None

    # Check if file is a zip file
    if not zipfile.is_zipfile(zip_file):
        print("File is not a zip file")
        return None

    # Print second attempt message if second_attempt flag is set
    if second_attempt:
        print(f"{'-' * 64}\nSecond attempt using OCR on images...\n{'-' * 64}")

    # Get file extension and initialize result variable
    extension = get_file_extension(zip_file)
    result = None

    # Process cbz or epub file (if second_attempt flag is set for epub)
    if extension == ".cbz" or (extension == ".epub" and second_attempt):
        # Parse the images in the zip file
        images = parse_zip_file(zip_file)
        # If no images are found, log error and return None
        if images is None:
            send_message(f"No images found in: {os.path.basename(zip_file)}")
            write_to_file("no_images.txt", os.path.basename(zip_file))
            return None

        # Loop through each image in the zip file and process for ISBN search
        relevant_images = [image for image in images if image]
        for image in relevant_images:
            extracted_texts = extract_text_from_image(image.data)
            if not extracted_texts:
                continue
            isbn = process_isbn_extraction(
                extracted_texts, image.name, zip_file, relevant_images
            )
            if isbn:
                result = process_book_match(isbn, zip_file, extracted_texts)
                if result:
                    return result

    # Process epub file (if second_attempt flag is not set)
    elif extension == ".epub":
        # Open the epub file
        with zipfile.ZipFile(zip_file, "r") as zip_ref:
            # Get the list of files in the epub
            file_list = zip_ref.namelist()

            # Prioritize certain files
            priority_files = [
                "content.opf",
                "package.opf",
                "standard.opf",
                "volume.opf",
                "copyright.xhtml",
            ]
            for internal_file in file_list[:]:
                if os.path.basename(internal_file) in priority_files:
                    file_list.remove(internal_file)
                    file_list.insert(0, internal_file)

            # Attempt to extract ISBN from file list, skipping some files
            isbn = process_isbn_extraction(
                str(file_list), zip_file, zip_file, file_list, skip=True
            )
            if isbn:
                result = process_book_match(isbn, zip_file, str(file_list))
                if result:
                    return result
            else:
                # Remove non-HTML/XML files from the list
                for item in file_list[:]:
                    extension = get_file_extension(item)
                    if not extension in internal_epub_extensions:
                        file_list.remove(item)
                # Process each HTML/XML file in the list for ISBN search
                for f in file_list:
                    extension = get_file_extension(f)
                    if extension in internal_epub_extensions:
                        text = zip_ref.read(f).decode("utf-8")
                        isbn = process_isbn_extraction(text, f, zip_file, file_list)
                        if isbn:
                            result = process_book_match(isbn, zip_file, text)
                            if result:
                                return result
        if result:
            return result
        else:
            return None


# Removes any folder names in the ignored_folders
def remove_ignored_folders(dirs):
    return [x for x in dirs if x not in ignored_folder_names]


# Retrieves the file extension on the passed file
def get_file_extension(file):
    return os.path.splitext(file)[1]


# Converts an array of strings into a single string separated by spaces.
def convert_array_to_string(array):
    return " ".join(array)


# Convert a writers object to a list of strings.
def convert_writers_object_to_string_array(obj):
    attributes = ["writer", "penciller", "inker", "letterer", "cover", "editor"]
    obj_strings = []

    for attr in attributes:
        if hasattr(obj, attr):
            names = getattr(obj, attr).name
            if names:
                obj_strings.extend([name.strip() for name in names])

    return obj_strings


def check_for_author_upgrade(writers_from_epub, writers_from_api):
    result = ""
    if writers_from_epub and writers_from_api:
        # if writers_from_api contains a comma, split it and add each item to writers_from_api
        if "," in writers_from_api:
            writers_from_api = writers_from_api.split(",")
            # strip whitespace from each item in writers_from_api
            writers_from_api = [item.strip() for item in writers_from_api]
            # remove any empty items from writers_from_api
            writers_from_api = [item for item in writers_from_api if item]
        epub_writers_string = convert_to_ascii(
            str(convert_writers_object_to_string_array(writers_from_epub))
        )
        if epub_writers_string:
            if not isinstance(writers_from_api, list):
                writers_from_api = [writers_from_api]
            for writer in writers_from_api[:]:
                writer = convert_to_ascii(writer)
                if writer and len(writer.split()) == 2:
                    flipped = " ".join(list(reversed(writer.split(" "))))
                    if re.search(
                        writer, epub_writers_string, re.IGNORECASE
                    ) or re.search(flipped, epub_writers_string, re.IGNORECASE):
                        # remove from epub_writers_string
                        for item in writers_from_api:
                            if re.search(
                                writer, convert_to_ascii(item), re.IGNORECASE
                            ) or re.search(flipped, item, re.IGNORECASE):
                                writers_from_api.remove(item)
                else:
                    if writer and re.search(writer, epub_writers_string, re.IGNORECASE):
                        # remove from epub_writers_string
                        for item in writers_from_api:
                            if re.search(writer, convert_to_ascii(item), re.IGNORECASE):
                                writers_from_api.remove(item)
        if writers_from_api:
            for item in writers_from_api:
                result += f"{item}, " if item != writers_from_api[-1] else item
    elif not writers_from_epub and writers_from_api:
        result = writers_from_api
    else:
        print("No writers found in epub or api")
    return result


# Runs various logic to determine whether or not the upgrade will be approved.
# def check_for_author_upgrade(writers_from_epub, writers_from_api):
#     result = ""

#     if not writers_from_epub and not writers_from_api:
#         print("No writers found in epub or api")
#         return result

#     if not writers_from_epub and writers_from_api:
#         return (
#             writers_from_api
#             if isinstance(writers_from_api, str)
#             else ", ".join(writers_from_api)
#         )

#     # if writers_from_api contains a comma, split it and add each item to writers_from_api
#     if "," in writers_from_api:
#         writers_from_api = [
#             item.strip() for item in writers_from_api.split(",") if item.strip()
#         ]

#     epub_writers_string = convert_to_ascii(
#         str(convert_writers_object_to_string_array(writers_from_epub))
#     )

#     if epub_writers_string:
#         if not isinstance(writers_from_api, list):
#             writers_from_api = [writers_from_api]

#         for writer in writers_from_api[:]:
#             writer = convert_to_ascii(writer)

#             if writer and len(writer.split()) == 2:
#                 flipped = " ".join(list(reversed(writer.split(" "))))

#                 if (
#                     writer.lower() in epub_writers_string.lower()
#                     or flipped.lower() in epub_writers_string.lower()
#                 ):
#                     # remove from epub_writers_string
#                     for item in writers_from_api:
#                         if (
#                             writer.lower() in convert_to_ascii(item).lower()
#                             or flipped.lower() in item.lower()
#                         ):
#                             writers_from_api.remove(item)
#             elif writer and writer.lower() in epub_writers_string.lower():
#                 # remove from epub_writers_string
#                 for item in writers_from_api:
#                     if writer.lower() in convert_to_ascii(item).lower():
#                         writers_from_api.remove(item)
#     if writers_from_api:
#         for item in writers_from_api:
#             result += f"{item}, " if item != writers_from_api[-1] else item

#     return result


# Checks for a published-date upgrade
def check_for_published_date_upgrade(published_date_from_epub, published_date_from_api):
    if len(published_date_from_api) == 4 and len(published_date_from_epub) > 4:
        return False

    # Ensure both dates have valid year, month, and day, zero-filling if needed
    def extract_date_parts(date_str):
        match = re.match(r"(\d{4})-(\d{1,2})-(\d{1,2})", date_str)
        if match:
            year, month, day = match.groups()
            return year, month.zfill(2), day.zfill(2)
        return "", "", ""

    epub_year, epub_month, epub_day = extract_date_parts(published_date_from_epub)
    api_year, api_month, api_day = extract_date_parts(published_date_from_api)

    if published_date_from_epub and published_date_from_api:
        if (epub_year, epub_month, epub_day) == (api_year, api_month, api_day):
            return False
        if published_date_from_epub != published_date_from_api:
            return True
    elif published_date_from_api and not published_date_from_epub:
        return True

    return False


class Data:
    def __init__(
        self,
        title,
        title_sort,
        author,
        publisher,
        series,
        languages,
        published_date,
        isbn,
        comments,
        number,
        average_rating,
        series_id,
        api_link,
        maturity_rating,
        genres,
        tags,
        zip_comment,
    ):
        self.title = title
        self.title_sort = title_sort
        self.author = author
        self.publisher = publisher
        self.series = series
        self.languages = languages
        self.published_date = published_date
        self.isbn = isbn
        self.comments = comments
        self.number = number
        self.average_rating = average_rating
        self.series_id = series_id
        self.api_link = api_link
        self.maturity_rating = maturity_rating
        self.genres = genres
        self.tags = tags
        self.zip_comment = zip_comment


# Parse the metadata text from ebook-meta command output.
def parse_ebook_meta(metadata_text):
    metadata = {}
    current_key = None
    lines = str(metadata_text).strip().split("\n")

    for line in lines:
        # Skip any empty lines
        if not line:
            continue

        if re.match(r"^(\w+(\(\w\))?((\s)+)?)(\w+(\(\w\))?((\s)+)?)?:", line):
            key, value = line.split(":", 1)  # split only on the first colon
            key = key.strip()
            value = value.strip()

            if current_key:
                metadata[current_key] = metadata[current_key].strip()

            current_key = key
            metadata[key] = value
        elif current_key:
            metadata[current_key] += f" {line.strip()}"

    if current_key:
        metadata[current_key] = metadata[current_key].strip()

    return metadata


cached_file_metadata = {}


# Retrieves the metadata from the file
def get_file_metadata(file_path):
    extension = get_file_extension(file_path)
    modification_time = os.path.getmtime(file_path)

    # Check if file metadata is already cached and up to date
    if file_path in cached_file_metadata:
        metadata, cached_modification_time = cached_file_metadata[file_path]
        if modification_time == cached_modification_time:
            return metadata

    # Retrieve metadata based on file extension and cache it
    metadata = []
    if extension == ".cbz" and contains_comic_info(file_path):
        metadata = get_cbz_metadata(file_path)
        # store the metadata in the cache
        cached_file_metadata[file_path] = (metadata, modification_time)
    elif extension == ".epub":
        metadata = get_epub_metadata(file_path)
        # store the metadata in the cache
        cached_file_metadata[file_path] = (metadata, modification_time)

    return metadata


# Get metadata from epub file using Calibre's ebook-meta command.
def get_epub_metadata(epub_path):
    command = ["ebook-meta", epub_path]
    data = execute_command(command)
    data = parse_ebook_meta(data)

    title = data.get("Title", "")
    title_sort = data.get("Title sort", "")
    author = data.get("Author(s)", "")
    publisher = data.get("Publisher", "")
    series = data.get("Series", "")
    languages = data.get("Languages", "")
    published_date = data.get("Published", "")
    identifiers = data.get("Identifiers", "")
    comments = data.get("Comments", "")
    average_rating = data.get("Rating", "")
    isbn = ""
    number = ""
    series_id = ""
    api_link = ""
    maturity_rating = ""
    zip_comment = get_zip_comment(epub_path)
    genres = data.get("Tags", [])

    if series:
        number_search = re.search(r"(#[0-9]+((\.[0-9]+)?)+)", series, re.IGNORECASE)
        if number_search:
            number = number_search.group()
            number = re.sub(r"#", "", number).strip()
            number = set_num_as_float_or_int(number)
        series = re.sub(r"(#[0-9]+((\.[0-9]+)?)+)", "", series).strip()

    if languages:
        languages = standardize_tag(languages)

    if published_date:
        date_match = re.match(
            r"(\d{4})(?:-(\d{1,2})(?:-(\d{1,2}))?)?(?:T.*)?", published_date
        )
        if date_match:
            year, month, day = date_match.groups()

            if month:
                month = month.zfill(2)
                if day:
                    day = day.zfill(2)
                    published_date = f"{year}-{month}-{day}"
                else:
                    published_date = f"{year}-{month}"
            else:
                published_date = year
        else:
            published_date = ""

    if identifiers:
        if re.search(r"(series_id:.*)", identifiers, re.IGNORECASE):
            series_id = re.search(r"(series_id:.*)", identifiers, re.IGNORECASE).group(
                0
            )
            if re.search(r"(series_id:.*,)", series_id, re.IGNORECASE):
                series_id = re.sub(r",.*", "", series_id).strip()

        isbn_search = re.search(rf"isbn:{isbn_13_regex}", identifiers, re.IGNORECASE)
        if isbn_search:
            isbn = isbn_search.group()
            isbn = re.sub(r"[^0-9]", "", isbn)

    if comments:
        comments = str(comments).replace("\u200b", "")

    if average_rating:
        average_rating = set_num_as_float_or_int(average_rating)

    if genres:
        genres = genres.split(", ")
        genres = sorted(genres)

    return Data(
        title,
        title_sort,
        author,
        publisher,
        series,
        languages,
        published_date,
        isbn,
        comments,
        number,
        average_rating,
        series_id,
        api_link,
        maturity_rating,
        genres,
        [],
        zip_comment,
    )


def clean_below_similarity_score(
    basename, array_list, volume_one_summary, require_summary_match=False
):
    # Initialize lists
    bases = [remove_punctuation(basename).strip()]
    volume_one_sentences = []

    # Process volume one summary sentences
    if volume_one_summary:
        volume_one_sentences = [
            sentence
            for sentence in sent_tokenize(volume_one_summary.strip())
            if len(sentence) >= 3
        ]
        if not volume_one_sentences:
            print("\tNo valid sentences found in volume one summary.")
    else:
        print("\tNo volume one summary passed in.")

    # Translate base name if required
    if translate_titles and not bases[0].isdigit() and not require_summary_match:
        try:
            clean_base_jp = ts.google(bases[0], to_language="ja")
            bases.append(clean_base_jp)
        except:
            print(f"\tFailed to translate: {bases[0]}")

    # Sort array_list based on the presence of the English title
    if len(array_list) > 1:
        array_list.sort(
            key=lambda item: getattr(item.title, "english", "") or "",
            reverse=True,
        )

    # Sort array_list based on the first letter of the English title
    first_letter_of_basename = re.search(r"^[a-zA-Z]", bases[0])
    if first_letter_of_basename:
        first_letter_of_basename = first_letter_of_basename.group()
        array_list.sort(
            key=lambda item: getattr(item.title, "english", "")
            .lower()
            .startswith(first_letter_of_basename.lower()),
            reverse=True,
        )

    # Loop through items in the array_list
    for item in array_list:
        sentences = []

        # Process item description sentences
        if hasattr(item, "description") and item.description:
            sentences = [
                sentence
                for sentence in sent_tokenize(item.description.strip())
                if len(sentence) >= 3
            ]
            if not sentences:
                print("\tNo valid sentences found in item description.")
        else:
            print("\tNo description found to split sentences from.")

        comparisons = []

        # Remove any item in volume_one_sentences and sentences where length is less than 3
        if volume_one_sentences and sentences:
            sentences = [
                re.sub(r"<[^>]*>", "", sentence).strip() for sentence in sentences
            ]

            # Compare each pair of sentences from volume_one_sentences and item_sentences
            for sentence in volume_one_sentences:
                for compare_sentence in sentences:
                    clean_sentence = remove_punctuation(sentence).strip()
                    clean_compare_sentence = remove_punctuation(
                        compare_sentence
                    ).strip()

                    if clean_sentence and clean_compare_sentence:
                        sentences_similarity_score = similar(
                            clean_sentence, clean_compare_sentence
                        )

                        if sentences_similarity_score >= sentence_similarity_score:
                            send_discord_message(
                                None,
                                "Sentence Match",
                                color=8421504,
                                fields=[
                                    {
                                        "name": "Sentence",
                                        "value": f'"{sentence}"',
                                        "inline": False,
                                    },
                                    {
                                        "name": "Compare Sentence",
                                        "value": f'"{compare_sentence}"',
                                        "inline": False,
                                    },
                                    {
                                        "name": "Score",
                                        "value": str(sentences_similarity_score),
                                        "inline": False,
                                    },
                                ],
                            )
                            return [item]

        if not require_summary_match:
            # Process and translate titles if required
            for title_type in ["english", "romaji", "native"]:
                if hasattr(item.title, title_type):
                    compare_name = remove_punctuation(
                        getattr(item.title, title_type)
                    ).strip()
                    if compare_name and compare_name not in comparisons:
                        comparisons.append(compare_name)

                        # Translate title if required
                        if translate_titles and not compare_name.isdigit():
                            try:
                                translated_title = (
                                    ts.google(compare_name, to_language="ja")
                                    if title_type == "romaji"
                                    else ts.google(compare_name, to_language="en")
                                )
                                if (
                                    translated_title
                                    and translated_title not in comparisons
                                ):
                                    comparisons.append(translated_title)
                                    print(
                                        f"\t\tTranslated {title_type.capitalize()}: {translated_title}"
                                    )
                            except Exception as e:
                                send_message(
                                    f"Failed to translate: {compare_name}", error=True
                                )

            # Process and translate synonyms if required
            if hasattr(item, "synonyms"):
                for synonym in item.synonyms:
                    compare_synonym = remove_punctuation(synonym).strip()
                    if compare_synonym and compare_synonym not in comparisons:
                        comparisons.append(compare_synonym)

                        # Translate synonym if required
                        if translate_titles and not compare_synonym.isdigit():
                            try:
                                translated_synonym = ts.google(
                                    compare_synonym, to_language="en"
                                )
                                if (
                                    translated_synonym
                                    and translated_synonym not in comparisons
                                ):
                                    comparisons.append(translated_synonym)
                            except Exception as e:
                                send_message(
                                    f"Failed to translate: {compare_synonym}",
                                    error=True,
                                )

            # Compare base names with comparisons and check similarity score
            for base in bases:
                for comparison in comparisons:
                    similarity_score = similar(
                        remove_punctuation(base), remove_punctuation(comparison)
                    )

                    if (
                        similarity_score >= required_similarity_score
                        or similarity_score >= 0.965
                    ):
                        return [item]
    return []


class AnilistResult:
    def __init__(
        self,
        country="",
        cover="",
        description="",
        description_short="",
        end_date="",
        genres="",
        id="",
        popularity="",
        score="",
        staff="",
        start_date="",
        status="",
        synonyms="",
        tags="",
        title={"romaji": "", "english": "", "native": ""},
        url="",
        volumes="",
        similarity_score="",
        local_image_path="",
    ):
        self.country = country
        self.cover = cover
        self.description = description
        self.description_short = description_short
        self.end_date = end_date
        self.genres = genres
        self.id = id
        self.popularity = popularity
        self.score = score
        self.staff = staff
        self.start_date = start_date
        self.status = status
        self.synonyms = synonyms
        self.tags = tags
        self.title = title
        self.url = url
        self.volumes = volumes
        self.similarity_score = similarity_score
        self.local_image_path = local_image_path


# Filters the results by the country specified
def filter_by_country(results, country_raws_regex):
    return [
        i
        for i in results
        if getattr(i, "country", None)
        and re.search(rf"{country_raws_regex}", i.country, re.IGNORECASE)
    ]


# Filters the results by the format specified
def filter_by_format(results, format_array):
    return [
        item
        for item in results
        if getattr(item, "format", None) and item.format in format_array
    ]


def filter_out_non_ids(results):
    new_results = [
        subitem
        for item in results
        for subitem in (item if isinstance(item, list) else [item])
        if hasattr(subitem, "id") and subitem.id
    ]
    return new_results


# Filters the results based on whether the first word in the basename matches the title or synonyms.
def filter_by_first_word(results, first_word):
    # default to returning all results
    filtered_results = results

    filtered_results = [
        x
        for x in results
        if (
            (
                hasattr(x, "title")
                and x.title
                and re.search(
                    first_word,
                    remove_punctuation(str(x.title)),
                    re.IGNORECASE,
                )
            )
            or (
                hasattr(x, "synonyms")
                and x.synonyms
                and re.search(
                    first_word,
                    remove_punctuation(str(x.synonyms)),
                    re.IGNORECASE,
                )
            )
        )
    ]

    return filtered_results


# Prints our anilist results
# as we filter step by step
# Makes it easier to see what is being filtered out
def print_titles(results):
    for result in results:
        # [format] [country] title
        print(
            f"\t\t\t[{str(result.format).upper()}] [{str(result.country).upper()}] {str(result.title)}"
        )


# Gives the user a short version of the title, if a dash or colon is present.
# EX: Series Name - Subtitle --> Series Name
def get_shortened_title(title):
    shortened_title = ""
    if ("-" in title or ":" in title) and re.search(r"((\s+(-)|:)\s+)", title):
        shortened_title = re.sub(r"((\s+(-)|:)\s+.*)", "", title).strip()
    return shortened_title


# Searches anilist for a matching series and returns it.
def search_anilist(basename, type_of_dir, cover_file_path, volume_one_summary):
    end_result = None
    ani_search_sleep_time = 10

    try:
        client = anilist.Client()

        # Print search message
        print(f"{'-' * 80}\nSearching Anilist: {basename} {type_of_dir}\n{'-' * 80}")

        # Prepare fields for Discord message
        fields = [
            {"name": "Search:", "value": basename, "inline": False},
            {"name": "Filter Type(s):", "value": str(type_of_dir), "inline": False},
        ]

        # Initialize variable for shortened search
        shortened_search_results = []
        search = []
        country_regex_filter = r"(jpn?|japan|japanese|kr|korea|korean)"
        additional_results = []

        # Get the Shortened Basename
        shortened_basename = get_shortened_title(basename)

        # Search with the Shortened Basename
        if shortened_basename:
            fields.insert(
                1,
                {
                    "name": "Shortened Search:",
                    "value": shortened_basename,
                    "inline": False,
                },
            )
            send_discord_message(
                None, "Searching Anilist", color=8421504, fields=fields
            )
            shortened_search = client.search_manga(shortened_basename, limit=10)
            time.sleep(ani_search_sleep_time)
            shortened_search = (
                filter_out_non_ids(shortened_search) if shortened_search else []
            )
            time.sleep(ani_search_sleep_time)
            shortened_search_results = [
                client.get_manga(i.id) for i in shortened_search
            ]
        else:
            send_discord_message(
                None, "Searching Anilist", color=8421504, fields=fields
            )
            time.sleep(ani_search_sleep_time)
            # Search for/with Basename
            search = client.search_manga(basename, limit=10)

        # Process shortened search results
        if shortened_search_results:
            print(f"\n\tShortened Starting Results: {len(shortened_search_results)}")
            print_titles(shortened_search_results)

            # Filter by country
            shortened_search_results = filter_by_country(
                shortened_search_results, country_regex_filter
            )

            print(
                f"\n\t\tCountry Results: {len(shortened_search_results)} ({country_regex_filter})"
            )
            print_titles(shortened_search_results)

            # Filter by format
            shortened_search_results = filter_by_format(
                shortened_search_results, type_of_dir
            )

            print(
                f"\n\t\tFormat Results: {len(shortened_search_results)} ({type_of_dir})"
            )
            print_titles(shortened_search_results)

            # Filter by similarity score
            shortened_search_results = clean_below_similarity_score(
                shortened_basename,
                shortened_search_results,
                volume_one_summary,
                require_summary_match=True,
            )

            print(f"\n\t\tSimilarity Score Results: {len(shortened_search_results)}")
            print_titles(shortened_search_results)

            if len(shortened_search_results) == 1:
                search = shortened_search_results
                send_message(
                    f"\n\t\tFound result using shortened basename: \n\t\t\t{shortened_search_results[0].title}",
                    discord=False,
                )
            else:
                if len(shortened_search_results) > 1:
                    additional_results = shortened_search_results
                # Reset whether it was empty or more than one
                shortened_search_results = []
                # Perform the long search if the short search didn't match
                time.sleep(ani_search_sleep_time)
                search = client.search_manga(basename, limit=10)

        # Process search results
        if search:
            id_results = []
            if shortened_search_results:
                id_results = shortened_search_results
            else:
                try:
                    for s in search:
                        if not isinstance(s, list):
                            continue

                        for item in s:
                            if item and hasattr(item, "id") and item.id:
                                id_results.append(client.get_manga(item.id))
                except Exception as e:
                    send_message(f"Error in search results: {e}", error=True)

                # Get manga results for all valid items
                # id_results = [
                #     client.get_manga(item.id)
                #     for s in search
                #     if isinstance(s, list)
                #     for item in s
                #     if item and hasattr(item, "id") and item.id
                # ]

                # Extend the additional results from the shortened search
                # if they are available
                if additional_results:
                    id_results.extend(additional_results)

                print(f"\n\tStarting Long Results: {len(id_results)}")
                print_titles(id_results)

                time.sleep(ani_search_sleep_time)

                # Filter by country
                id_results_country_filter = filter_by_country(
                    id_results, country_regex_filter
                )

                print(
                    f"\n\t\tCountry Results: {len(id_results_country_filter)} ({country_regex_filter})"
                )
                print_titles(id_results_country_filter)

                # Filter by format
                filter_results_format = filter_by_format(
                    id_results_country_filter, type_of_dir
                )

                print(
                    f"\n\t\tFormat Results: {len(filter_results_format)} ({type_of_dir})"
                )
                print_titles(filter_results_format)

                # Filter by similarity score
                filter_results_sim_score = clean_below_similarity_score(
                    basename, filter_results_format, volume_one_summary
                )

                print(
                    f"\n\t\tSimilarity Score Results: {len(filter_results_sim_score)}"
                )
                print_titles(filter_results_sim_score)

                # Get the first word in the basename
                first_word_in_base_name = (
                    re.search(r"\w+", remove_punctuation(basename)).group()
                    if re.search(r"\w+", remove_punctuation(basename))
                    else ""
                )

                id_results_filtered_first_word = filter_results_sim_score

                # Filter by first word in the basename, if we have a first_word_in_base_name
                if first_word_in_base_name:
                    id_results_filtered_first_word = filter_by_first_word(
                        filter_results_sim_score, first_word_in_base_name
                    )
                    print(
                        f"\n\t\tFirst Word Results: {len(id_results_filtered_first_word)} ({first_word_in_base_name})"
                    )
                    print_titles(id_results_filtered_first_word)

                # Reassign id_results
                id_results = filter_results_sim_score

            print(f"\n\n\tFinal Results: {len(id_results)}\n")
            print_titles(id_results)

            matches = []

            if id_results:
                for data in id_results:
                    anilist_result = AnilistResult()
                    anilist_result.format_type = type_of_dir

                    # Define a list of attribute names
                    ATTRIBUTES = [
                        "country",
                        "cover",
                        "description",
                        "description_short",
                        "end_date",
                        "genres",
                        "id",
                        "popularity",
                        "score",
                        "staff",
                        "start_date",
                        "status",
                        "synonyms",
                        "tags",
                        "title",
                        "url",
                        "volumes",
                    ]

                    # Loop over each attribute and set the value on the result object
                    for attr in ATTRIBUTES:
                        value = getattr(data, attr, "")
                        setattr(
                            anilist_result,
                            attr,
                            (
                                sorted(value)
                                if attr in ["tags", "genres"]
                                and isinstance(value, list)
                                else value
                            ),
                        )

                    # Determine if the result is a match
                    if len(id_results) == 1:
                        anilist_result.similarity_score = 0
                        matches.append(anilist_result)
                    elif (
                        anilist_result.cover
                        and anilist_result.title
                        and cover_file_path
                        and os.path.isfile(cover_file_path)
                    ):
                        online_image_link = anilist_result.cover
                        sizes = ["extra_large", "large", "medium", "small", "tiny"]

                        # Get the images from each size
                        images = [
                            getattr(online_image_link, size)
                            for size in sizes
                            if hasattr(online_image_link, size)
                        ]

                        # Get the scores from the images
                        if len(images) == 1:
                            score = process_image_link_temp_for_anilist(
                                cover_file_path, online_image_link
                            )
                        else:
                            scores = [
                                score_result
                                for link in images
                                if (
                                    score_result := process_image_link_temp_for_anilist(
                                        cover_file_path, link
                                    )
                                )
                            ]

                        score = max(scores) if scores else 0

                        # Check for a valid score
                        if not score:
                            send_message("Score does not have a value!")
                        # Check if the score is above the required score
                        elif score >= required_image_ssim_score:
                            anilist_result.similarity_score = score
                            matches.append(anilist_result)
                    else:
                        send_message("\tNo cover file found")

            else:
                send_message("\tNo results found")

            if matches:
                best_match = max(matches, key=lambda x: x.similarity_score)
                best_match.local_image_path = cover_file_path

                print(f"\n\t\t{'-' * 53}\n\t\tBest Match: {basename}\n\t\t{'-' * 53}")
                print(f"\t\tTitle ID: {best_match.id}")
                print(f"\t\tTitles: {best_match.title}")
                print(f"\t\tGenres: {best_match.genres}")
                print(f"\t\tTags: {best_match.tags}")
                print(f"\t\tURL: {best_match.url}")
                print(f"\t\tOnline Image URL: {best_match.cover.extra_large}")
                if best_match.similarity_score:
                    print(
                        f"\t\t{'-' * 53}\n\t\tSSIM Score: {best_match.similarity_score}\n\t\t{'-' * 53}\n"
                    )
                else:
                    print(
                        f"\t\t{'-' * 53}\n\t\tMatched through one result remaining.\n\t\t{'-' * 53}\n"
                    )

                end_result = best_match
            else:
                send_message("\t\tNo matches found.")
        else:
            send_message("\tNo search results found.")
    except Exception as e:
        send_message(f"Anilist search failed: {e}", error=True)

    if not end_result:
        write_to_file(
            "no_search_results_from_anilist.txt",
            basename,
            without_timestamp=True,
            check_for_dup=True,
        )

    return end_result


# find file that is named cover in list of files
def find_cover_file(path):
    cover = ""
    if os.path.isfile(path):
        cover = next(
            (
                get_extensionless_name(path) + extension
                for extension in image_extensions
                if os.path.isfile(get_extensionless_name(path) + extension)
            ),
            "",
        )
    else:
        send_message(
            f"\tPassed file does not exist when searching for cover file: {path}",
            error=True,
        )
    return cover


# convert list of strings to a single string seperated by commas
def list_to_string(list):
    return ", ".join(list)


# compare metadata between the api result and the local epub file
def compare_metadata(book, epub_path, files):
    global result_subtitles

    if not write_metadata_to_file:
        send_message("\tMetadata Write is not enabled")
        send_message("\tSkipping Metadata Write")
        return

    extension = get_file_extension(epub_path)

    # Initialize variables
    data = ""
    zip_comments_to_be_written = []
    cbz_changes = []
    data_comparison = []
    anilist_metadata = ""
    cover_file_path = find_cover_file(epub_path)
    vol_one_check = False

    # Get metadata from the ebook file
    if extension == ".epub":
        data = get_epub_metadata(epub_path)
    elif extension == ".cbz":
        data = get_cbz_metadata(epub_path)

    # Check if the book is volume one and has a series and cover file
    if isinstance(book.volume, list):
        if 1 in book.volume:
            vol_one_check = True
    elif book.volume == 1:
        vol_one_check = True

    if vol_one_check and book.series:
        # Search AniList for metadata
        anilist_metadata = search_anilist(
            book.series,
            ["NOVEL"] if extension == ".epub" else ["MANGA", "ONE_SHOT"],
            cover_file_path,
            book.summary,
        )

        # Print the result if found
        if anilist_metadata:
            print_book_result(anilist_metadata, anilist=True)

            # Update book metadata if AniList metadata exists
            if anilist_metadata.genres:
                book.genres = anilist_metadata.genres
            if anilist_metadata.tags:
                book.tags = anilist_metadata.tags
            if anilist_metadata.status:
                book.status = anilist_metadata.status
            if anilist_metadata.volumes:
                book.volume_count = anilist_metadata.volumes

    try:
        print(f"\n{'-' * 32}Metadata Check{'-' * 34}")
        updated = False

        # Add the subtitle to the list of subtitles
        # Prevents duplicate subtitles from being used
        if book.subtitle and book.subtitle not in result_subtitles:
            result_subtitles.append(PossibleSubtitle("title", book.subtitle))

        # Check if the book subtitle is a duplicate
        if (
            book.title
            and not book.title.lower().startswith("volume")
            and check_description_match(
                file_descriptions, book.title, volume.series_name
            )
        ):
            volume_keyword = "Volumes" if isinstance(book.volume, list) else "Volume"
            book.title = f"{volume_keyword} {convert_array_to_string_with_dashes(book.volume) if isinstance(book.volume, list) else book.volume}"
            if book.part:
                book.title += f" Part {book.part}"

        if book.subtitle and not check_description_match(
            file_descriptions, book.subtitle, volume.series_name
        ):
            contains_series = re.search(rf"{book.series}", book.subtitle, re.IGNORECASE)
            subtitle_in_series = re.search(
                rf"{book.subtitle}", book.series, re.IGNORECASE
            )
            contains_exclusions = any(
                re.search(exclusion, book.subtitle, re.IGNORECASE)
                for exclusion in subtitle_exclusion_keywords
            )

            if (
                not contains_series
                and not subtitle_in_series
                and not contains_exclusions
            ):
                if data.title != book.subtitle:
                    updated = True
                    if extension == ".epub":
                        update_metadata(
                            "ebook-meta",
                            epub_path,
                            data.title,
                            book.subtitle,
                            "Title",
                            "-t",
                        )
                    else:
                        cbz_changes.append(
                            "title=" + re.sub(r"([,=])", r"^\1", book.subtitle)
                        )
                        data_comparison.append(data.title)
            elif book.title and data.title != book.title:
                updated = True
                if extension == ".epub":
                    update_metadata(
                        "ebook-meta", epub_path, data.title, book.title, "Title", "-t"
                    )
                else:
                    cbz_changes.append("title=" + re.sub(r"([,=])", r"^\1", book.title))
                    data_comparison.append(data.title)
        elif book.title and data.title != book.title:
            updated = True
            if extension == ".epub":
                update_metadata(
                    "ebook-meta", epub_path, data.title, book.title, "Title", "-t"
                )
            else:
                cbz_changes.append("title=" + re.sub(r"([,=])", r"^\1", book.title))
                data_comparison.append(data.title)

        if not updated and only_update_if_new_title:
            print(
                "\tonly_update_if_new_title = True\n\t\tNo new available titles, skipping..."
            )
            return

        # formatting still remains from bookwalker scraper, formatting does not remain when reading in file
        # thus it will infinitely rewrite unless I remove it, this is only a band-aid fix
        if extension == ".cbz" and re.search(
            "bookwalker|kobo", book.api_link, re.IGNORECASE
        ):
            book_sum_compare = re.sub(r"(\t|\n|\r)", "", book.summary)
        else:
            book_sum_compare = book.summary
        if convert_to_ascii(book_sum_compare) != convert_to_ascii(data.comments):
            print_diff(data.comments, book.summary)
            if extension == ".epub":
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    data.comments,
                    book.summary,
                    "Summary",
                    "-c",
                )
            else:
                cbz_changes.append(
                    "comments=" + re.sub(r"([,=])", r"^\1", book.summary)
                )
                data_comparison.append(data.comments)
        if data.isbn != book.isbn and book.isbn != 0:
            if extension == ".epub":
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    str(data.isbn),
                    book.isbn,
                    "ISBN",
                    "--isbn",
                )
        if book.isbn:
            zip_comments_to_be_written.append(f"isbn:{book.isbn}")

        if book.google_volume_id:
            zip_comments_to_be_written.append(f"volume_id:{book.google_volume_id}")

        if extension == ".cbz":
            author_upgrade_result = check_for_author_upgrade(data.credits, book.writer)
            if author_upgrade_result:
                book.writer = author_upgrade_result
                # if book.writer contains a comma, split it
                if re.search(r",", book.writer):
                    writer_list = book.writer.split(",")
                    # remove any whitespace from the list
                    writer_list = [x.strip() for x in writer_list]
                    # remove any empty strings from the list
                    writer_list = [x for x in writer_list if x]
                    for writer in writer_list:
                        data_comparison.append(
                            str(convert_writers_object_to_string_array(data.credits))
                        )
                        cbz_changes.append(
                            "credit=Writer:" + re.sub(r"([,=])", r"^\1", writer)
                        )
                else:
                    data_comparison.append(
                        str(convert_writers_object_to_string_array(data.credits))
                    )
                    cbz_changes.append(
                        "credit=Writer:" + re.sub(r"([,=])", r"^\1", book.writer)
                    )
        elif (
            extension == ".epub"
            and data.author
            and re.search(r"\band\b", data.author, re.IGNORECASE)
        ):
            seperated = re.sub(
                r"((\s+)?([\(\{\[])(.*)([\]\}\)])(\s+)?)", "", data.author
            ).strip()
            seperated = re.split(r"(\band\b|&)", seperated, flags=re.IGNORECASE)
            seperated = [
                x for x in seperated if not re.search(r"\band\b|&", x, re.IGNORECASE)
            ]
            seperated = [
                re.sub(r"((\s+)?([\(\{\[])(.*)([\]\}\)])(\s+)?)", "", x).strip()
                for x in seperated
            ]
            seperated = [re.sub(r"[^\w\s]", "", x).strip() for x in seperated]
            formatted = ""
            for item in seperated:
                formatted += f"{item}&" if item != seperated[-1] else item

            update_metadata(
                "ebook-meta",
                epub_path,
                data.author,
                formatted,
                "Authors",
                "-a",
            )
        if (
            data.published_date != book.published_date
            and check_for_published_date_upgrade(
                data.published_date, book.published_date
            )
        ):
            if extension == ".epub":
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    data.published_date,
                    book.published_date,
                    "Date",
                    "-d",
                )
            else:
                if book.year != data.year:
                    cbz_changes.append(f"year={book.year}")
                    data_comparison.append(str(data.year))
                if book.month != data.month:
                    cbz_changes.append(f"month={book.month}")
                    data_comparison.append(str(data.month))
                if book.day != data.day:
                    cbz_changes.append(f"day={book.day}")
                    data_comparison.append(str(data.day))

        if data.languages != book.language:
            if extension == ".epub":
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    data.languages,
                    book.language,
                    "Language",
                    "-l",
                )
            else:
                cbz_changes.append(
                    "language=" + re.sub(r"([,=])", r"^\1", book.language)
                )
                data_comparison.append(data.languages)
        if book.publisher and data.publisher != book.publisher:
            if extension == ".epub":
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    data.publisher,
                    book.publisher,
                    "Publisher",
                    "-p",
                )
            else:
                cbz_changes.append(
                    "publisher=" + re.sub(r"([,=])", r"^\1", book.publisher)
                )
                data_comparison.append(data.publisher)

        if book.series != data.series:
            if extension == ".epub":
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    data.series,
                    book.series,
                    "Series",
                    "--series",
                )
            else:
                cbz_changes.append("series=" + re.sub(r"([,=])", r"^\1", book.series))
                data_comparison.append(data.series)

        updated = False

        issue_string = ""
        if book.part:
            if isinstance(book.number, list):
                book.number = f"{book.number[0]}.{book.part}"
            else:
                book.number = f"{book.number}.{book.part}"
            book.number = float(book.number)
        elif isinstance(book.number, list):
            if extension == ".epub":
                book.number = book.number[0]
            elif extension == ".cbz":
                for number in book.number:
                    issue_string += (
                        f"{number}-" if number != book.number[-1] else str(number)
                    )

        book_num_check = book.number
        if isinstance(book.number, list):
            book_num_check = book.number[0]
        else:
            book_num_check = book.number
        if data.number != book_num_check:
            if extension == ".epub":
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    data.number,
                    book.number,
                    "Index Number",
                    "-i",
                )
        if extension == ".cbz" and data.issue != book.number:
            if not issue_string:
                cbz_changes.append(f"issue={book.number}")
            else:
                cbz_changes.append(f"issue={issue_string}")
            data_comparison.append(data.issue)
        if (
            extension == ".cbz"
            and str(book.status).lower() in ["finished", "cancelled"]
            and book.volume_count
            and data.volume_count != book.volume_count
        ):
            cbz_changes.append(f"issue_count={book.volume_count}")
            data_comparison.append(data.volume_count)
        if data.average_rating != book.average_rating and book.average_rating:
            if extension == ".epub":
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    data.average_rating,
                    book.average_rating * 2,
                    "Rating",
                    "-r",
                    half=True,
                )
            elif extension == ".cbz":
                # cbz_changes.append(f"crtical_rating={float(book.average_rating)}")
                # data_comparison.append(data.average_rating)
                pass

        if book.series_id:
            zip_comments_to_be_written.append(book.series_id)

        if anilist_metadata:
            if anilist_metadata.id:
                zip_comments_to_be_written.append(f"anilist_id:{anilist_metadata.id}")
            if data.genres != book.genres:
                if extension == ".epub":
                    update_metadata(
                        "ebook-meta",
                        epub_path,
                        data.genres,
                        list_to_string(book.genres),
                        "Genres",
                        "--tags",
                    )
                else:
                    cbz_changes.append(
                        "genre="
                        + re.sub(r"([,=])", r"^\1", list_to_string(book.genres))
                    )
                    data_comparison.append(list_to_string(data.genres))
            if data.tags != book.tags:
                if extension == ".epub":
                    pass
                else:
                    pass
                    # cbz_changes.append(
                    #     "tag=" + re.sub(r"([,=])", r"^\1", list_to_string(book.tags))
                    # )
                    # data_comparison.append(list_to_string(data.tags))

        if (
            data.maturity_rating != book.maturity_rating
            and book.maturity_rating == "MATURE"
            and data.maturity_rating != "M"
            and extension == ".cbz"
        ):
            cbz_changes.append("maturity_rating=M")
            data_comparison.append(data.maturity_rating)
        if extension == ".cbz":
            if data.api_link != book.api_link:
                cbz_changes.append(
                    "web_link=" + re.sub(r"([,=])", r"^\1", book.api_link)
                )
                data_comparison.append(data.api_link)
            custom_note = re.sub(
                r"([,=])",
                r"^\1",
                f"Tagged on {datetime.now().date()}",
            )
            if cbz_changes and data.notes != custom_note:
                cbz_changes.append(f"notes={custom_note}")
                data_comparison.append(data.notes)

        if cbz_changes and data_comparison:
            update_metadata(
                "comictagger",
                epub_path,
                data_comparison,
                cbz_changes,
                "CBZ Archive",
                "-s -t cr -m",
                skip_print=True,
                cbz=True,
            )
        if zip_comments_to_be_written:
            fields = []
            # add string "Identifiers" to the beginning of the list
            combined = "Identifiers: "
            for item in zip_comments_to_be_written:
                combined += (
                    f"{item}, " if item != zip_comments_to_be_written[-1] else item
                )

                # split on :
                if re.search(r":", item):
                    fields.append(
                        {
                            "name": titlecase(replace_underscores(item.split(":")[0])),
                            "value": item.split(":")[1],
                            "inline": False,
                        }
                    )

            up_to_date_zip_comment = get_zip_comment(epub_path)
            if combined and up_to_date_zip_comment != str(combined):
                print(f"\tZip Comment: {combined}\n")
                if fields:
                    # Capitilize all words four letters or less
                    for field in fields:
                        field["name"] = " ".join(
                            [
                                word.upper() if len(word) <= 4 else word
                                for word in field["name"].split()
                            ]
                        )
                    send_discord_message(
                        None,
                        "Zip Comment",
                        color=8421504,
                        fields=fields,
                    )
                print(
                    f"\tUpdating Zip Comment: \n\t\tFrom:  {up_to_date_zip_comment} \n\t\tTo:    {combined}"
                )
                if (
                    (manualmetadata or skip_updating_metadata)
                    and manual_zip_comment_approval
                    and data.zip_comment != combined
                ):
                    if "series_id" in data.zip_comment and "series_id" not in combined:
                        identifiers = get_identifiers(data.zip_comment)
                        series_id = [x for x in identifiers if "series_id" in x]
                        if series_id:
                            print(
                                f"\n\tSeries ID Link: https://play.google.com/store/books/series?id={series_id[0].split(':')[1]}\n"
                            )
                    if len(combined) < len(data.zip_comment):
                        while True:
                            user_input = input("\t\tApprove? (y/n): ").strip().lower()
                            if user_input == "y":
                                result = write_zip_comment(epub_path, combined)
                                break
                            elif user_input == "n":
                                print("\t\t\tUpdate declined.")
                                return
                            else:
                                print("\tInvalid input. Please enter 'y' or 'n'.")
                    else:
                        result = write_zip_comment(epub_path, combined)

                else:
                    result = write_zip_comment(epub_path, combined)

                if result:
                    print("\t\t\tUpdate successful.")
                else:
                    send_message(
                        f"Error updating zip comment for {epub_path}.", error=True
                    )
    except Exception as e:
        send_message(f"Error in metadata comparison: {e}", error=True)
        write_to_file("isbn_script_errors.txt", str(e))
    print(f"{'-' * 80}")


def update_metadata(
    command,
    epub_path,
    data_num,
    book_num,
    item,
    argument,
    skip_print=False,
    half=False,
    cbz=False,
):
    try:
        item_title = titlecase(replace_underscores(item))
        if not cbz:
            if not skip_print:
                print(f"\tUpdating {item_title}: ")
                if not half:
                    print(f"\t\tFrom: {data_num}\n\t\tTo: {book_num}")
                else:
                    if book_num:
                        print(f"\t\tFrom: {data_num}\n\t\tTo: {book_num / 2}")
                    else:
                        print(f"\t\tFrom: {data_num}\n\t\tTo: {book_num}")

            if item.lower() in ["rating", "index number"]:
                book_num = str(book_num)

        elif cbz and (len(data_num) == len(book_num)):
            count = len(data_num)
            for num in range(count):
                y_clean = re.sub(r"(\^)([,=])", r"\2", book_num[num])
                y_clean = y_clean.split("=", 1)
                old_value = data_num[num]
                print(
                    ("\tUpdating" if y_clean[0] != "credit" else "\tAdding")
                    + f" {y_clean[0].capitalize()}: "
                )
                print(f"\t\tFrom: {old_value}\n\t\tTo: {y_clean[1]}")
        else:
            print(f"\tUpdating {item_title}: ")
            print(f"\t\tFrom: {data_num}\n\t\tTo: {book_num}")

        combined = ", ".join(book_num) if cbz else book_num
        command = command.split(" ")
        argument = argument.split(" ")

        if cbz:
            command.extend(argument)
            command.append(combined)
            command.append(epub_path)
        else:
            command.append(epub_path)
            command.extend(argument)
            command.append(combined)

        execution_result = ""
        similarity_score = 0

        if manualmetadata and not skip_updating_metadata:
            if manual_meta_similarity_skip and data_num and book_num:
                similarity_score = similar(str(data_num), str(book_num))

            if similarity_score < 0.90:
                user_input = None

                while user_input not in ["y", "n"]:
                    user_input = input("\tApprove? (y/n): ")
                if user_input == "y":
                    execution_result = execute_command(command)
                elif user_input == "n":
                    print("\t\tUpdated declined.")
                    return
            else:
                execution_result = execute_command(command)

        elif skip_updating_metadata:
            print("\tSkipping Metadata Update\n")
            return
        else:
            execution_result = execute_command(command)

        lower_execution = execution_result.lower()
        was_successful = (
            "changed metadata" in lower_execution
            or "successful match" in lower_execution
        )
        was_error = "warning:" in lower_execution or "error" in lower_execution

        if execution_result and was_successful and not was_error:
            print("\t\tSuccessfully updated\n")
        else:
            send_message(
                f"\t\tFailed to update {item_title} for {epub_path}.\n\t\tCommand: {command}"
                + (f"\n\t\t{execution_result}" if was_error else "")
            )
            if not was_error:
                send_message(
                    "\t\tDo you have calibre/comictagger installed?",
                    error=True,
                )
    except Exception as e:
        send_message(f"Error updating metadata: {e}", error=True)
        write_to_file("isbn_script_errors.txt", str(e))


# Preps the image for comparison
def preprocess_image(image):
    # Convert to grayscale
    gray_image = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
    # Apply histogram equalization
    gray_image = cv2.equalizeHist(gray_image)
    # Normalize the image
    gray_image = gray_image / 255.0
    return gray_image


# Comapres two images using SSIM
def compare_images(imageA, imageB):
    try:
        # Preprocess images
        grayA = preprocess_image(imageA)
        grayB = preprocess_image(imageB)

        print(f"\t\t\t\t\tOnline Size: {imageA.shape}")
        print(f"\t\t\t\t\tCover Size: {imageB.shape}")

        # Compute SSIM between the two images
        ssim_score = ssim(grayA, grayB, data_range=1.0)

        print(f"\t\t\t\tSSIM: {ssim_score}")
        return ssim_score
    except Exception as e:
        print(f"Error comparing images: {e}")
        return 0


# Checks similarity between two strings.
@lru_cache(maxsize=None)
def similar(a, b):
    # convert to lowercase and strip
    a = a.lower().strip()
    b = b.lower().strip()

    # evaluate
    if a == "" or b == "":
        return 0.0
    elif a == b:
        return 1.0
    else:
        return SequenceMatcher(None, a, b).ratio()


# Pre-compile dual space removal
dual_space_pattern = re.compile(r"(\s{2,})")


# Replaces any pesky double spaces
@lru_cache(maxsize=None)
def remove_dual_space(s):
    if "  " not in s:
        return s

    return dual_space_pattern.sub(" ", s)


# Removes common words to improve string matching accuracy between a series_name
# from a file name, and a folder name, useful for when releasers sometimes include them,
# and sometimes don't.
@lru_cache(maxsize=None)
def normalize_str(
    s,
    skip_common_words=False,
    skip_editions=False,
    skip_type_keywords=False,
    skip_japanese_particles=False,
    skip_misc_words=False,
    skip_storefront_keywords=False,
):
    if len(s) <= 1:
        return s

    words_to_remove = []

    if not skip_common_words:
        common_words = [
            "the",
            "a",
            "à",
            "and",
            "&",
            "I",
            "of",
        ]
        words_to_remove.extend(common_words)

    if not skip_editions:
        editions = [
            "Collection",
            "Master Edition",
            "(2|3|4|5)-in-1 Edition",
            "Edition",
            "Exclusive",
            "Anniversary",
            "Deluxe",
            # "Omnibus",
            "Digital",
            "Official",
            "Anthology",
            "Limited",
            "Complete",
            "Collector",
            "Ultimate",
            "Special",
        ]
        words_to_remove.extend(editions)

    if not skip_type_keywords:
        # (?<!^) = Cannot start with this word.
        # EX: "Book Girl" light novel series.
        type_keywords = [
            "(?<!^)Novel",
            "(?<!^)Light Novel",
            "(?<!^)Manga",
            "(?<!^)Comic",
            "(?<!^)LN",
            "(?<!^)Series",
            "(?<!^)Volume",
            "(?<!^)Chapter",
            "(?<!^)Book",
            "(?<!^)MANHUA",
        ]
        words_to_remove.extend(type_keywords)

    if not skip_japanese_particles:
        japanese_particles = [
            "wa",
            "o",
            "mo",
            "ni",
            "e",
            "de",
            "ga",
            "kara",
            "to",
            "ya",
            r"no(?!\.)",
            "ne",
            "yo",
        ]
        words_to_remove.extend(japanese_particles)

    if not skip_misc_words:
        misc_words = [r"((\d+)([-_. ]+)?th)", "x", "×", "HD"]
        words_to_remove.extend(misc_words)

    if not skip_storefront_keywords:
        storefront_keywords = [
            r"Book(\s+)?walker",
        ]
        words_to_remove.extend(storefront_keywords)

    for word in words_to_remove:
        pattern = rf"\b{word}\b" if word not in type_keywords else rf"{word}\s"
        s = re.sub(pattern, " ", s, flags=re.IGNORECASE).strip()

        s = remove_dual_space(s)

    return s.strip()


# Removes the s from any words that end in s
@lru_cache(maxsize=None)
def remove_s(s):
    return re.sub(r"\b(\w+)(s)\b", r"\1", s, flags=re.IGNORECASE).strip()


# Precompiled
punctuation_pattern = re.compile(r"[^\w\s+]")


# Determines if the string contains punctuation
def contains_punctuation(s):
    return bool(punctuation_pattern.search(s))


# Returns a string without punctuation.
@lru_cache(maxsize=None)
def remove_punctuation(s):
    return re.sub(r"[^\w\s+]", " ", s).strip()


# Determines if the string contains unicode characters.
# or rather non-ascii characters.
def contains_unicode(input_str):
    return not input_str.isascii()


# Cleans the string by removing punctuation, bracketed info, and replacing underscores with periods.
# Converts the string to lowercase and removes leading/trailing whitespace.
@lru_cache(maxsize=None)
def clean_str(
    string,
    skip_lowercase_convert=False,
    skip_colon_replace=False,
    skip_bracket=False,
    skip_unidecode=False,
    skip_normalize=False,
    skip_punctuation=False,
    skip_remove_s=False,
    skip_convert_to_ascii=False,
    skip_underscore=False,
):
    # Convert to lower and strip
    s = string.lower().strip() if not skip_lowercase_convert else string

    # replace : with space
    s = s.replace(":", " ") if not skip_colon_replace and ":" in s else s

    # remove uneccessary spacing
    s = remove_dual_space(s)

    # Remove bracketed info
    s = remove_brackets(s) if not skip_bracket and contains_brackets(s) else s

    # Remove unicode
    s = unidecode(s) if not skip_unidecode and contains_unicode(s) else s

    # normalize the string
    s = normalize_str(s) if not skip_normalize else s

    # Remove punctuation
    s = remove_punctuation(s) if not skip_punctuation and contains_punctuation(s) else s

    # remove trailing s
    s = remove_s(s) if not skip_remove_s else s

    # remove dual spaces
    s = remove_dual_space(s)

    # convert to ascii
    s = convert_to_ascii(s) if not skip_convert_to_ascii else s

    # Replace underscores with periods
    s = replace_underscores(s) if not skip_underscore and "_" in s else s

    return s.strip()


# detect language of the passed string using langdetect
@lru_cache(maxsize=None)
def detect_language(s):
    language = ""
    if s and len(s) >= 5 and re.search(r"[\p{L}\p{M}]+", s):
        try:
            language = detect(s)
        except Exception as e:
            send_message(str(e), error=True)
            return language
    return language


# convert string to acsii
@lru_cache(maxsize=None)
def convert_to_ascii(s):
    return "".join(i for i in s if ord(i) < 128)


class Person:
    def __init__(self, role, name, primary=False):
        self.role = role
        self.name = name
        self.primary = primary


class Credits:
    def __init__(self, writer, penciller, inker, letterer, cover, editor):
        self.writer = writer
        self.penciller = penciller
        self.inker = inker
        self.letterer = letterer
        self.cover = cover
        self.editor = editor


class CBZTags:
    def __init__(
        self,
        isbn,
        series_id,
        series,
        issue,
        title,
        publisher,
        published_date,
        year,
        month,
        day,
        number,
        web_link,
        scan_info,
        comments,
        notes,
        credits,
        languages,
        zip_comment,
        api_link,
        characters,
        manga,
        maturity_rating,
        average_rating,
        teams,
        genres,
        tags,
        volume_count,
    ):
        self.isbn = isbn
        self.series_id = series_id
        self.series = series
        self.issue = issue
        self.title = title
        self.publisher = publisher
        self.published_date = published_date
        self.year = year
        self.month = month
        self.day = day
        self.number = number
        self.web_link = web_link
        self.scan_info = scan_info
        self.comments = comments
        self.notes = notes
        self.credits = credits
        self.languages = languages
        self.zip_comment = zip_comment
        self.api_link = api_link
        self.characters = characters
        self.manga = manga
        self.maturity_rating = maturity_rating
        self.average_rating = average_rating
        self.teams = teams
        self.genres = genres
        self.tags = tags
        self.volume_count = volume_count


# dynamically parse all tags from comicinfo.xml and return a dictionary of the tags
def parse_comicinfo_xml(xml_file):
    tags = {}
    if xml_file:
        try:
            tree = ET.fromstring(xml_file)
            tags = {child.tag: child.text for child in tree}
        except Exception as e:
            send_message(
                f"Attempted to parse comicinfo.xml: {xml_file}\nERROR: {e}",
                error=True,
            )
            return tags
    return tags


# parse comictagger output
def parse_manga_meta(metadata_text):
    metadata = {}
    current_key = None
    credits = []

    # Split the metadata text into lines
    lines = metadata_text.strip().split("\n")
    for line in lines:
        line = line.strip()

        # Skip any empty lines
        if not line:
            continue

        if re.match(r"^\w+:", line):
            # Split the line into key and value using the first colon
            key, value = line.split(":", 1)
            key = key.strip()
            value = value.strip()

            # If the key is "credit", add the value to the credits list
            if key.lower() == "credit":
                current_key = key
                credits.append(value)
            else:
                # If there is a current key, store its value in metadata
                if current_key:
                    metadata[current_key] = metadata[current_key].strip()

                # Set the new current key and store its initial value
                current_key = key
                metadata[key] = value
        else:
            if current_key:
                # If no colon is found, add the line to the current key's value
                if current_key != "credit":
                    metadata[current_key] += f" {line.strip()}"
                else:
                    credits[-1] += f" {line.strip()}"

    # Store the last key's value in metadata
    if current_key and current_key != "credit":
        metadata[current_key] = metadata[current_key].strip()

    # Add the credits list to metadata
    metadata["credits"] = credits
    return metadata


def get_cbz_metadata(path):
    # Define the command to execute
    command = [
        "comictagger",
        "-p",
        "-t",
        "cr",
        path,
    ]

    # Get the zip comment
    zip_comment = get_zip_comment(path)

    # Execute the command and get the metadata text
    metadata_text = execute_command(command)

    if not metadata_text:
        return None

    # Parse the metadata text
    data = parse_manga_meta(metadata_text)

    # Get the values from the data dictionary using default values
    isbn = data.get("isbn", "")
    series_id = data.get("series_id", "")
    series = data.get("series", "")
    issue = data.get("issue", "")
    title = data.get("title", "")
    publisher = data.get("publisher", "")
    published_date = data.get("published_date", "")
    year = data.get("year", "")
    month = data.get("month", "")
    day = data.get("day", "")
    volume = data.get("volume", "")
    web_link = ""
    scan_info = data.get("scan_info", "")
    characters = data.get("characters", "")
    comments = data.get("comments", "")
    notes = data.get("notes", "")
    credits = data.get("credits", "")
    languages = data.get("language", "")
    api_link = data.get("api_link", "")
    manga = data.get("manga", "")
    maturity_rating = data.get("maturity_rating", "")
    average_rating = data.get("average_rating", "")
    critical_rating = data.get("critical_rating", "")
    teams = data.get("teams", "")
    genres = data.get("genre", [])
    tags = data.get("tags", [])
    volume_count = data.get("issue_count", 0)

    # Process the credits list and create a Credits object
    credit_types = {
        "writer": Person("Writer", [], primary=True),
        "penciller": Person("Penciller", []),
        "inker": Person("Inker", []),
        "letterer": Person("Letterer", []),
        "cover": Person("Cover", []),
        "editor": Person("Editor", []),
    }

    for credit in credits:
        if ":" not in credit:
            continue

        key, value = credit.split(":", 1)
        key = key.strip().lower()
        value = value.strip()

        if key in credit_types:
            credit_types[key].name.append(value)

    credit_obj = Credits(
        credit_types["writer"],
        credit_types["penciller"],
        credit_types["inker"],
        credit_types["letterer"],
        credit_types["cover"],
        credit_types["editor"],
    )

    if issue:
        if "-" not in issue:
            issue = set_num_as_float_or_int(issue)
        else:
            issue = [set_num_as_float_or_int(x) for x in get_min_and_max_numbers(issue)]

    if volume:
        if "-" not in volume:
            volume = set_num_as_float_or_int(volume)
        else:
            volume = [
                set_num_as_float_or_int(x) for x in get_min_and_max_numbers(volume)
            ]

    if languages:
        languages = standardize_tag(languages)

    if characters:
        characters = [x.strip() for x in characters.split(",")]

    if average_rating:
        average_rating = set_num_as_float_or_int(average_rating)

    if critical_rating:
        average_rating = set_num_as_float_or_int(critical_rating)

    if genres:
        genres = [x.strip() for x in genres.split(",")]
        genres = sorted(genres)

    if tags:
        tags = [x.strip() for x in tags.split(",")]
        tags = sorted(tags)

    if volume_count:
        volume_count = int(volume_count)

    if year:
        published_date = year
        if month:
            published_date += f"-{month.zfill(2)}"
            if day:
                published_date += f"-{day.zfill(2)}"

    if zip_comment:
        series_id_search = re.search(r"(series_id:.*)", zip_comment, re.IGNORECASE)
        if series_id_search:
            series_id = series_id_search.group()
            if re.search(r"(series_id:.*,)", series_id, re.IGNORECASE):
                series_id = re.sub(r",.*", "", series_id).strip()

        isbn = re.search(rf"{isbn_13_regex}", zip_comment, re.IGNORECASE)
        isbn = re.sub(r"[^0-9]", "", isbn.group()) if isbn else ""

    if data.get("web_link", ""):
        api_link = data.get("web_link", "")

    # Create a CBZTags object and return it
    return CBZTags(
        isbn,
        series_id,
        series,
        issue,
        title,
        publisher,
        published_date,
        year,
        month,
        day,
        volume,
        web_link,
        scan_info,
        comments,
        notes,
        credit_obj if credits else "",
        languages,
        zip_comment,
        api_link,
        characters,
        manga,
        maturity_rating,
        average_rating,
        teams,
        genres,
        tags,
        volume_count,
    )


# Result class that is used for our image_comparison results from our
# image comparison function
class Image_Result:
    def __init__(self, book, ssim_score, image_link):
        self.book = book
        self.ssim_score = ssim_score
        self.image_link = image_link


def clean_api_results(
    results,
    vol_num,
    first_word,
    multi_volume,
    series,
    extension,
    part,
    skip_vol_nums_equal=False,
    skip_contains_first_word=False,
    skip_omnibus_check=False,
    skip_manga_keyword_check=False,
    skip_series_similarity=False,
    skip_isebook_check=False,
    skip_categories_check=False,
    skip_summary_check=False,
    series_similarity_score=0.4,
    skip_language_check=False,
):
    if not results:
        return []

    if not isinstance(results, list):
        results = [results]

    new_results = []
    print(f"\nFiltering Results [{len(results)}]:")

    for idx, r in enumerate(results, 1):
        print(
            f"\t[{idx}/{len(results)}]: [{r.title} - {r.series}] - {r.isbn} {r.categories}"
        )
        print(f"\t\tLink: {r.api_link}")
        passed = True

        try:
            # Check if the volume numbers are equal
            if not skip_vol_nums_equal:
                title_vol_num = get_release_number_cache(r.title)
                if (
                    (title_vol_num == vol_num or r.volume == vol_num)
                    or (title_vol_num == int(vol_num) or r.volume == int(vol_num))
                ) and r.part == part:
                    print("\t\tPassed volume num check")
                else:
                    print("\t\tFailed volume num check")
                    continue

            # Check if the first word is in the series
            if not skip_contains_first_word:
                if re.search(
                    unidecode(first_word),
                    remove_punctuation(unidecode(r.series)),
                    re.IGNORECASE,
                ):
                    print("\t\tPassed first word check")
                else:
                    print(
                        f"\t\tFailed first word check\n\t\t\tFirst Word: {first_word}\n\t\t\tSeries: {r.series}"
                    )
                    continue

            # Check if the omnibus status matches
            if not skip_omnibus_check:
                is_omnibus = re.search(
                    r"omnibus|omni-bus",
                    f"{r.series} {r.title}",
                    re.IGNORECASE,
                )
                if (
                    multi_volume
                    and (
                        is_omnibus
                        or (
                            check_for_multi_volume_file(r.series)
                            or check_for_multi_volume_file(r.title)
                        )
                    )
                ) or (not multi_volume and not is_omnibus):
                    print("\t\tPassed omnibus check")
                else:
                    print(
                        f"\t\tFailed omnibus check\n\t\t\tSeries: {r.series}\n\t\t\tTitle: {r.title}"
                    )
                    continue

            # Check if the title contains manga or light novel keywords
            if not skip_manga_keyword_check:
                if not re.search(
                    "manga" if extension == ".epub" else "light novel",
                    f"{r.title} {r.series}",
                    re.IGNORECASE,
                ):
                    print("\t\tPassed keyword check")
                else:
                    print(
                        f"\t\tFailed manga/light novel keyword check\n\t\t\tTitle: {r.title}\n\t\t\tSeries: {r.series}"
                    )
                    continue

            # Check if the series names are similar enough
            if not skip_series_similarity:
                score = similar(
                    remove_punctuation(series),
                    remove_punctuation(
                        re.sub(
                            r"\(.*\)",
                            "",
                            r.series,
                        )
                    ),
                )
                if score >= series_similarity_score:
                    print("\t\tPassed series similarity check")
                else:
                    print(
                        f"\t\tFailed series check\n\t\t\tScore: {score}\n\t\t\tResult Series: {r.series}\n\t\t\tSeries: {series}"
                    )
                    continue

            # Check if the book is an ebook (digital, not physical)
            if not skip_isebook_check:
                if r.is_ebook:
                    print("\t\tPassed is_ebook check")
                elif square_enix_bypass and re.search(
                    r"^(?=.*Square)(?=.*Enix).*$", r.publisher, re.IGNORECASE
                ):
                    print(
                        "\n\t\tis_ebook=False \n\t\t\tpublisher is square-enix, exception made, using paperback metadata."
                    )
                else:
                    print("\t\tFailed is_ebook check")
                    continue

            # Check if the book is in the correct categories
            if not skip_categories_check:
                if r.categories:
                    passed = any(
                        re.search(
                            (
                                "Fiction|Novel|Light Novel"
                                if extension == ".epub"
                                else "Comic|Graphic|Manga"
                            ),
                            category,
                            re.IGNORECASE,
                        )
                        for category in r.categories
                    )
                print(
                    "\t\t"
                    + ("Passed" if passed else "Failed")
                    + f" {'fiction' if extension == '.epub' else 'comic/graphic'} category check"
                )

                if not passed:
                    print("\t\tFailed Categories check")
                    continue

            # Check if the summary is present and doesn't contain chapter titles
            if not skip_summary_check:
                if not r.summary or re.search(
                    r"(Chapter([-_. ]+)?Titles.*)", r.summary, re.IGNORECASE
                ):
                    print("\t\tFailed summary check")
                    print(f"\t\t\tSummary: {r.summary}")
                    continue
                else:
                    print("\t\tPassed summary check")

            # Check if the language is English
            if not skip_language_check:
                acceptable_languages = ["en", "eng", "english"]

                if r.language:
                    if r.language.lower() in acceptable_languages or (
                        r.summary and detect_language(r.summary) == "en"
                    ):
                        print("\t\tPassed language check")
                        if r.language not in acceptable_languages:
                            r.language = "en"
                    else:
                        print("\t\tFailed language check")
                        print(f"\t\t\tLanguage: {r.language}")
                        continue
                elif r.summary:
                    detected_language = detect_language(r.summary)

                    if detected_language in acceptable_languages:
                        print("\t\tPassed language check")
                        if r.language not in acceptable_languages:
                            r.language = "en"
                    else:
                        print("\t\tFailed language check")
                        print(
                            f"\t\t\tDetected Language on Summary: {detected_language}"
                        )
                        continue
                else:
                    print("\t\tFailed language check")
                    continue

        except Exception as e:
            send_message(f"Error processing result: {e}", error=True)
            continue

        # Check if it passed all checks
        print(f"\t\t{'-' * 5}Passed all checks{'-' * 5}")
        new_results.append(r)

    return new_results


# Precompile the regular expressions
rx_remove = re.compile(
    r".*(%s)([-_. ]|)([-_. ]|)([0-9]+)(\b|\s)" % volume_regex_keywords,
    re.IGNORECASE,
)
rx_search_part = re.compile(r"(\b(Part)([-_. ]|)([0-9]+)\b)", re.IGNORECASE)
rx_search_chapters = re.compile(
    r"([0-9]+)(([-_.])([0-9]+)|)+((x|#)([0-9]+)(([-_.])([0-9]+)|)+)", re.IGNORECASE
)
rx_remove_x_hash = re.compile(r"((x|#))", re.IGNORECASE)


# Retrieves and returns the file part from the file name
@lru_cache(maxsize=None)
def get_file_part(file, chapter=False, series_name=None, subtitle=None):
    result = ""

    contains_keyword = (
        re.search(r"\bpart\b", file, re.IGNORECASE) if "part" in file.lower() else ""
    )
    contains_indicator = "#" in file or "x" in file

    if not contains_keyword and not contains_indicator:
        return result

    if series_name:
        # remove it from the file name
        file = re.sub(re.escape(series_name), "", file, flags=re.IGNORECASE).strip()
    if subtitle:
        # remove it from the file name
        file = re.sub(re.escape(subtitle), "", file, flags=re.IGNORECASE).strip()

    if not chapter:
        if contains_keyword:
            # Remove the matched string from the input file name
            file = rx_remove.sub("", file).strip()
            search = rx_search_part.search(file)
            if search:
                result = search.group(1)
                result = re.sub(
                    r"Part([-_. ]|)+", " ", result, flags=re.IGNORECASE
                ).strip()
    else:
        if contains_indicator:
            search = rx_search_chapters.search(file)
            if search:
                part_search = re.search(
                    r"((x|#)([0-9]+)(([-_.])([0-9]+)|)+)", search.group(), re.IGNORECASE
                )
                if part_search:
                    # remove the x or # from the string
                    result = rx_remove_x_hash.sub("", part_search.group())

    # Set the number as float or int
    result = set_num_as_float_or_int(result)

    return result


def get_search_keyword(s):
    s = normalize_str(s)
    word_list = s.split()

    return word_list[1] if len(word_list) >= 2 else word_list[0]


# DELETE AFTER RECODING OTHER PROCESS IMAGE LINK METHOD
def process_image_link_temp_for_anilist(cover_path, link):
    try:
        # read the images
        cover_image = cv2.imread(cover_path)

        # download online image
        online_image = requests.get(link).content
        online_image = Image.open(io.BytesIO(online_image))
        online_image = np.array(online_image)

        # if the images aren't the same size, resize them
        if online_image.shape[0] > cover_image.shape[0]:
            online_image = cv2.resize(
                online_image,
                (
                    cover_image.shape[1],
                    cover_image.shape[0],
                ),
            )
        else:
            cover_image = cv2.resize(
                cover_image,
                (
                    online_image.shape[1],
                    online_image.shape[0],
                ),
            )

        # if they have both have a third channel, make them the same
        if len(online_image.shape) == 3 and len(cover_image.shape) == 3:
            if online_image.shape[2] > cover_image.shape[2]:
                online_image = online_image[:, :, : cover_image.shape[2]]
            else:
                cover_image = cover_image[:, :, : online_image.shape[2]]
        elif len(online_image.shape) == 3 and len(cover_image.shape) == 2:
            online_image = online_image[:, :, 0]
        elif len(online_image.shape) == 2 and len(cover_image.shape) == 3:
            cover_image = cover_image[:, :, 0]

        # compare the images
        return compare_images(online_image, cover_image)
    except Exception as e:
        send_message(f"Error processing image link for anilist: {e}", error=True)
        return None


def process_image_link(
    result, cover_path, link, internal_cover_data, session_result_data, provider_name
):
    global image_link_cache

    def load_image_from_bytes(image_data):
        return np.array(Image.open(io.BytesIO(image_data)))

    def load_image_from_path(path):
        return cv2.imread(path)

    def fetch_online_image(url, provider_name):
        fetch_headers = {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/58.0.3029.110 Safari/537.3"
        }

        if provider_name not in ["kobo", "barnes_and_noble"]:
            response = requests.get(url, headers=fetch_headers, timeout=10)
            time.sleep(0.25)
            response.raise_for_status()  # Ensure we raise an error for bad status codes
            return response.content
        else:
            options = [
                "--disable-blink-features=AutomationControlled",
                "--window-size=7680,4320",
                "--start-maximized",
                "--headless",
                "--disable-gpu",
                "--no-sandbox",
                "--disable-dev-shm-usage",
                "user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
                "accept-language=en-US,en;q=0.9",
            ]
            driver = get_page_driver(link, options)
            if not driver:
                return None

            try:
                time.sleep(3)

                # Use JavaScript to get the image data
                image_data_base64 = driver.execute_script(
                    """
                    var img = document.querySelector('img');
                    if (img) {
                        var canvas = document.createElement('canvas');
                        var ctx = canvas.getContext('2d');
                        canvas.width = img.width;
                        canvas.height = img.height;
                        ctx.drawImage(img, 0, 0);
                        return canvas.toDataURL('image/png').split(',')[1];
                    } else {
                        return '';
                    }
                """
                )

                if not image_data_base64:
                    raise ValueError("Image data is empty or image not found.")

                # Decode base64 data
                image_data = base64.b64decode(image_data_base64)

                return image_data

            finally:
                driver.quit()

    def resize_images(img1, img2, desired_width=400, desired_height=600):
        img1_resized = cv2.resize(
            img1, (desired_width, desired_height), interpolation=cv2.INTER_AREA
        )
        img2_resized = cv2.resize(
            img2, (desired_width, desired_height), interpolation=cv2.INTER_AREA
        )
        return img1_resized, img2_resized

    def match_image_channels(img1, img2):
        if len(img1.shape) == 3 and len(img2.shape) == 3:
            min_channels = min(img1.shape[2], img2.shape[2])
            img1, img2 = img1[:, :, :min_channels], img2[:, :, :min_channels]
        elif len(img1.shape) == 3 and len(img2.shape) == 2:
            img1 = img1[:, :, 0]
        elif len(img1.shape) == 2 and len(img2.shape) == 3:
            img2 = img2[:, :, 0]
        return img1, img2

    # Load cover image from internal data or file path
    cover_image = None
    if internal_cover_data:
        cover_image = load_image_from_bytes(internal_cover_data)
    elif cover_path:
        cover_image = load_image_from_path(cover_path)

    online_image_data = None
    if image_link_cache and session_result_data:
        cached_item = next(
            (item for item in image_link_cache if item.image_link == link), None
        )
        if cached_item:
            online_image_data = cached_item.image_data

    print(
        f"\t\t\tImage Link {result.image_links.index(link) + 1} of {len(result.image_links)}"
    )
    print(f"\t\t\t\tImage Link: {link}")

    if not online_image_data:
        try:
            online_image_data = fetch_online_image(link, provider_name)
            if session_result_data:
                image_link_cache_item = ImageLinkCache(link, online_image_data)
                if image_link_cache_item not in image_link_cache:
                    image_link_cache.append(image_link_cache_item)
        except Exception as e:
            send_message(f"Error fetching online image: {e}", error=True)
            return None

    online_image = load_image_from_bytes(online_image_data)

    # Resize images to the smaller of the two
    online_image, cover_image = resize_images(online_image, cover_image)

    # Match image channels
    online_image, cover_image = match_image_channels(online_image, cover_image)

    score = compare_images(online_image, cover_image)

    return Image_Result(result, score, link)


# our session objects, one for each domain
session_objects = {}


# Returns a session object for the given URL
def get_session_object(url):
    domain = urlparse(url).netloc.split(":")[0]
    if domain not in session_objects:
        # Create a new session object and set a default User-Agent header
        session_object = requests.Session()
        session_object.headers.update(
            {
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/58.0.3029.110 Safari/537.36"
            }
        )
        session_objects[domain] = session_object
    return session_objects[domain]


# Makes a GET request to the given URL using a reusable session object,
# and returns a BeautifulSoup object representing the parsed HTML response.
def scrape_url(url, strainer=None, headers=None, cookies=None, proxy=None, timeout=10):
    try:
        session_object = get_session_object(url)

        # Create a dictionary of request parameters with only non-None values
        request_params = {
            "url": url,
            "headers": headers,
            "cookies": cookies,
            "proxies": proxy,
            "timeout": timeout,
        }
        response = session_object.get(
            **{k: v for k, v in request_params.items() if v is not None}
        )

        # Raise an exception if the status code indicates rate limiting
        if response.status_code == 403:
            send_message(
                f"Error scraping URL: {url}\nStatus Code: {response.status_code}",
                error=True,
            )
            return None

        soup = None
        if strainer:
            # Use the strainer to parse only specific parts of the HTML document
            soup = BeautifulSoup(response.content, "lxml", parse_only=strainer)
        else:
            soup = BeautifulSoup(response.content, "lxml")

        return soup
    except requests.exceptions.RequestException as e:
        send_message(f"Error scraping URL: {e}", error=True)
        return None


# Function to click the "Scroll Next" button until the end
def click_next_buttons(driver):
    buttons = driver.find_elements(
        By.XPATH, '//button[@aria-label="Show more volumes"]'
    )
    if not buttons:
        print("\t\t\tNo buttons, attempting to scrape IDs without clicking.")
        return False

    for i, button in enumerate(buttons):
        while True:
            html_before = driver.page_source
            try:
                driver.execute_script("arguments[0].click();", button)
                time.sleep(4)
                html_after = driver.page_source
                if html_before == html_after:
                    break
            except Exception as e:
                if i == len(buttons) - 1:
                    return False
                break
    return True


# Function to click the "Show more volumes" button until the end
# to load all available volumes into memory
def click_show_more_button(driver):
    wait = WebDriverWait(driver, 5)

    while True:
        try:
            # Wait for the button to appear
            button = wait.until(
                EC.element_to_be_clickable(
                    (By.XPATH, '//button[@aria-label="Show more volumes"]')
                )
            )

            # Scroll into view (optional but helpful)
            driver.execute_script("arguments[0].scrollIntoView(true);", button)
            time.sleep(1)  # Allow time for scrolling

            # Click the button using JavaScript to avoid issues
            driver.execute_script("arguments[0].click();", button)
            time.sleep(2)  # Allow time for content to load

            print("\t\t\tClicked 'Show more volumes' button.")

        except Exception:
            print(
                "\t\t\tNo more 'Show more volumes' button found. Finished loading all items."
            )
            break  # Exit loop when button is no longer found

    return True


# Function to scrape series IDs
@lru_cache(maxsize=None)
def scrape_series_ids(id, sort=False):
    url = f"https://play.google.com/store/books/series?id={id}"
    search_results = set()

    options = [
        "--disable-blink-features=AutomationControlled",
        "--window-size=7680,4320",
        "--start-maximized",
        "--headless",
        "--disable-gpu",
        "--no-sandbox",
        "--disable-dev-shm-usage",
    ]
    driver = get_page_driver(url, options)
    if not driver:
        return []

    if click_show_more_button(driver):
        print("\tScraped IDs with clicking.")
    else:
        print("\tScraped IDs without clicking.")

    # Parse the final page source
    soup = BeautifulSoup(driver.page_source, "lxml")
    ids = get_series_ids(soup, sort=sort)

    if ids:
        search_results.update(ids)
    else:
        print("\tNo IDs found")

    driver.quit()
    return list(set(search_results))


# Retrieves the ids from the soup passed, and returns them.
def get_series_ids(soup, sort=True):
    ids = set()
    if not soup:
        print("\tsoup is None")
        return list(ids)

    hrefs = soup.find_all("a", href=True)
    if not hrefs:
        print("\tNo hrefs found")
        return list(ids)

    filtered_hrefs = [href for href in hrefs if "/store/books/details" in href["href"]]

    cleaned_hrefs = set()
    for item in filtered_hrefs:
        href = item["href"]
        number_part = href.split("?")[0].rsplit("_", 1)[-1]
        number = re.sub(r"[^0-9]", "", number_part)
        id_match = re.search(r"id=(.*)", href)
        if id_match:
            id = id_match.group(1)
            if number.isdigit():
                number = number.zfill(3)
            cleaned_hrefs.add((href, number, id))

    if sort:
        cleaned_hrefs = sorted(cleaned_hrefs, key=lambda x: x[1])

    if not cleaned_hrefs:
        print("\tNo cleaned hrefs")
        return list(ids)

    ids.update(id for _, _, id in cleaned_hrefs)

    return list(ids)


# Gets the user a webdriver object based on the url passed in
def get_page_driver(url, options=[]):
    # Set the location of the chrome driver. using Service, with chrome_driver_location
    service = ChromeService(ChromeDriverManager().install())
    # service = ChromeService(chrome_driver_location)

    # Create the options object
    chrome_options = webdriver.ChromeOptions()

    # Add the options
    if options:
        for option in options:
            chrome_options.add_argument(option)

    # Create the driver
    driver = webdriver.Chrome(service=service, options=chrome_options)

    # Get the page
    driver.get(url)

    return driver


# gets the user passed result from an epub file
def get_meta_from_file(file, search_regex, extension):
    result = None
    if extension == ".epub":
        with zipfile.ZipFile(file, "r") as zf:
            for name in zf.namelist():
                if name.endswith(".opf"):
                    opf_file = zf.open(name)
                    opf_file_contents = opf_file.read()
                    lines = opf_file_contents.decode("utf-8")
                    search = re.search(search_regex, lines, re.IGNORECASE)
                    if search:
                        result = search.group()
                        if not re.search(r"subject", search_regex, re.IGNORECASE):
                            result = re.sub(r"<\/?.*>", "", result)
                        if re.search(r"(series_id:.*,)", result, re.IGNORECASE):
                            result = re.sub(r",.*", "", result).strip()
                        break
    elif extension == ".cbz":
        zip_comment = get_zip_comment(file)
        if zip_comment:
            search = re.search(search_regex, zip_comment, re.IGNORECASE)
            if search:
                result = search.group()
                search_two = re.search(search_regex, result, re.IGNORECASE)
                if search_two:
                    result = search_two.group()
                else:
                    result = ""
                if re.search(r"(series_id:.*,)", result, re.IGNORECASE):
                    result = re.sub(r",.*", "", result).strip()
    return result


# Pre-combiled remove_brackets() patterns
bracket_removal_pattern = re.compile(
    r"((((?<!-|[A-Za-z]\s|\[)(\[[^\]]*\]|\([^\)]*\)|\{[^}]*\})(?!-|\s*[A-Za-z]|\]))(\s+)?)+|([\[\{\(]((\d{4}))[\]\}\)]))",
    re.IGNORECASE,
)
bracket_avoidance_pattern = re.compile(r"^[\(\[\{].*[\)\]\}]$")
bracket_against_extension_pattern = re.compile(
    r"(\[[^\]]*\]|\([^\)]*\)|\{[^}]*\})(\.\w+$)"
)


# Removes bracketed content from the string, alongwith any whitespace.
# As long as the bracketed content is not immediately preceded or followed by a dash.
@lru_cache(maxsize=None)
def remove_brackets(string):
    # Avoid a string that is only a bracket
    # Probably a series name
    # EX: [(OSHI NO KO)]
    if (
        starts_with_bracket(string)
        and ends_with_bracket(string)
        and bracket_avoidance_pattern.search(string)
    ):
        return string

    # Remove all grouped brackets as long as they aren't surrounded by dashes,
    # letters, or square brackets.
    # Regex 1: ([\[\{\(]((\d{4}))[\]\}\)]) - FOR YEAR
    # Regex 2: (((?<!-|[A-Za-z]\s|\[)(\[[^\]]*\]|\([^\)]*\)|\{[^}]*\})(?!-|\s*[A-Za-z]|\]))(\s+)?)+ - FOR EVERYTHING ELSE
    string = bracket_removal_pattern.sub("", string).strip()

    # Get file extension
    ext = get_file_extension(string)

    if ext:
        # Remove ending bracket against the extension
        # EX: test (digital).cbz -> test .cbz
        string = (
            bracket_against_extension_pattern.sub(r"\2", string).strip()
            if contains_brackets(string)
            else string
        )

        # Remove the extension
        # EX: test.cbz -> test
        string = string.replace(ext, "").strip()

        # Re-add the extension
        # EX: test -> test.cbz
        string = f"{string}{ext}"

    # Return the modified string
    return string


# Converts a date string in the format "Month day, year" to "yyyy-mm-dd"
# EX: March 16, 2021 -> 2021-03-16
def convert_date_to_yyyy_mm_dd(date_string):
    if not date_string:
        return None

    date_string = date_string.strip()
    date = datetime.strptime(date_string, "%B %d, %Y")

    year = str(date.year)
    month = str(date.month)
    day = str(date.day)

    if len(month) == 1:
        month = f"0{month}"

    if len(day) == 1:
        day = f"0{day}"

    return {
        "date": f"{year}-{month}-{day}",
        "year": year,
        "month": month,
        "day": day,
    }


# Retrieves metadata from kobo books.
def get_kobo_books_meta(
    website_url, isbn, volume_number, part, series_name="", text_search=False
):
    try:
        image_link = ""
        rating = ""
        categories = []
        title = ""
        writer = ""
        series_link = ""
        summary = ""
        published_date = ""
        year = ""
        month = ""
        day = ""
        language = ""
        publisher = ""

        if not text_search:
            website_url = f"{website_url}/us/en/search?query={isbn}"
        else:
            print(f"\t{website_url}")

        options = [
            "--disable-blink-features=AutomationControlled",
            "--window-size=7680,4320",
            "--start-maximized",
            "--headless",
            "--disable-gpu",
            "--no-sandbox",
            "--disable-dev-shm-usage",
            "user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
            "accept-language=en-US,en;q=0.9",
        ]
        driver = get_page_driver(website_url, options)
        if not driver:
            return None

        soup = BeautifulSoup(driver.page_source, "lxml")

        # filter by div class "inner-wrap content-main"
        kobo_isbn_soup = soup.find("div", {"class": "inner-wrap content-main"})

        # contains image, rating, category, series name, title, writer, series link, summary
        if kobo_isbn_soup:
            primary_left_container = kobo_isbn_soup.find(
                "div", {"class": "primary-left-container"}
            )
            # find h1 class title product-field
            if primary_left_container:
                series = primary_left_container.find(
                    "h1", {"class": "title product-field"}
                )
                if series and not series_name:
                    series_name = series.text.strip()
                    series_name = remove_brackets(series_name)
                    if volume_number == "":
                        volume_search = re.search(
                            r"([0-9]+(\.?[0-9]+)?([-_][0-9]+\.?[0-9]+)?)$",
                            series_name,
                        )
                        if volume_search:
                            volume_number = volume_search.group(1)
                            if re.search(r"-", volume_number):
                                volume_number = get_min_and_max_numbers(volume_number)
                            else:
                                volume_number = set_num_as_float_or_int(volume_number)
                        elif (
                            not contains_volume_keywords(series_name)
                            and not contains_chapter_keywords(series_name)
                            and not re.search(r"([0-9]+)", series_name)
                        ):
                            volume_number = 1
                    if not part:
                        part_search = get_file_part(series_name)
                        if part_search:
                            part = part_search
                else:
                    print("\t\tNo series name found")
                subtitle_product_field = primary_left_container.find(
                    "span", {"class": "subtitle product-field"}
                )
                # if subtitle_product_field:
                #     title = subtitle_product_field.text.strip()
                # else:
                #     print("\t\tNo subtitle product-field found")
                #     print("\t\tNo title found on page.")
                writer = primary_left_container.find("a", {"class": "contributor-name"})
                if writer:
                    writer = titlecase(writer.text.strip())
                else:
                    print("\t\tNo writer found")
                series_link = primary_left_container.find(
                    "span", {"class": "product-sequence-field"}
                )
                if series_link:
                    series_link = series_link.find("a")
                    if series_link:
                        series_link = series_link["href"]
                        if series_link:
                            series_link = f"https://www.kobo.com{series_link}"
                else:
                    print("\t\tNo series link found")
                synopsis_description = primary_left_container.find(
                    "div", {"class": "synopsis-description"}
                )
                if synopsis_description:
                    # find all <p> in synopsis_description
                    paragraphs = synopsis_description.find_all("p")
                    if paragraphs:
                        # if multiple paragraphs, get the second one, otherwise get the first one
                        if len(paragraphs) > 1:
                            # create one big string out of all of the paragraphs, one p per line
                            for p in paragraphs:
                                summary += f"{p.text.strip()}\n"
                        else:
                            synopsis_description = paragraphs[0]
                            summary = synopsis_description.text.strip()
                    else:
                        # find all li in synopsis_description
                        lists = synopsis_description.find_all("li")
                        if lists:
                            # if multiple lists, get the second one, otherwise get the first one
                            if len(lists) > 1:
                                # create one big string out of all of the lists, one li per line
                                for li in lists:
                                    summary += f"{li.text.strip()}\n"
                            else:
                                synopsis_description = lists[0]
                                summary = synopsis_description.text.strip()
                    if summary:
                        summary = unidecode(summary)
                        title_search_in_summary = get_title_from_description(summary)
                        if title_search_in_summary:
                            title = titlecase(title_search_in_summary)
                        elif volume_number != "" and part:
                            title = f"Volume {volume_number} Part {part}"
                        elif volume_number != "" and not part:
                            title = f"Volume {volume_number}"
                else:
                    print("\t\tNo synopsis description found")
                inner_top_container = primary_left_container.find(
                    "div", {"class": "inner-top-container"}
                )
                if inner_top_container:
                    main_product_image = inner_top_container.find(
                        "div", {"class": "main-product-image"}
                    )
                    if main_product_image:
                        image = main_product_image.find("img")
                        if image:
                            image_link = image["src"]
                            if image_link:
                                image_link = f"https:{image_link}"
                    else:
                        print("\t\tNo main product image found")
                    # find ul class category-rankings inside inner-top-container
                    category_rankings = inner_top_container.find(
                        "ul", {"class": "category-rankings"}
                    )
                    if category_rankings:
                        # find all meta tags inside category-rankings
                        meta_tags = category_rankings.find_all("meta")
                        if meta_tags:
                            for meta in meta_tags:
                                # find content attribute of meta tag
                                if meta.has_attr("content"):
                                    categories.append(meta["content"])
                        else:
                            print("\t\tNo meta tags found")
                    else:
                        print("\t\tNo category rankings found")
                    # if categories:
                    #     category_combined_string = ""
                    #     if len(categories) > 1:
                    #         for category in categories:
                    #             category_combined_string += f"{category}, " if category != categories[-1] else category
                    #     else:
                    #         category_combined_string = categories[0]
                    #     categories = category_combined_string
                else:
                    print("\t\tNo inner top container found")

            # find div class rating-review-summary-header
            else:
                print("\t\tNo primary-left-container found.")
                return None
            rating_review_summary_header = kobo_isbn_soup.find(
                "div", {"class": "rating-review-summary-header"}
            )
            if rating_review_summary_header:
                # find span class average-rating
                average_rating = rating_review_summary_header.find(
                    "span", {"class": "average-rating"}
                )
                if average_rating:
                    # find all spans inside of average-rating
                    spans = average_rating.find_all("span")
                    if spans:
                        # get contents of first span
                        rating = spans[0].text.strip()
                        rating = set_num_as_float_or_int(rating)
                        if rating == 0 or rating > 10:
                            rating = ""
                        if rating > 5 and rating <= 10:
                            rating = rating / 2
                else:
                    print("\t\tNo average rating found")
            else:
                print("\t\tNo rating-review-summary-header found.")
            # find dib class bookitem-secondary-metadata
            bookitem_secondary_metadata = kobo_isbn_soup.find(
                "div", {"class": "bookitem-secondary-metadata"}
            )
            if bookitem_secondary_metadata:
                # find ul
                ul = bookitem_secondary_metadata.find("ul")
                if ul:
                    # find all li inside of ul
                    li = ul.find_all("li")
                    if li:
                        contents = []
                        for l in li:
                            contents.append(l.text.strip())
                        if contents:
                            publisher = re.sub(
                                r"(.*:)", "", contents[0], re.IGNORECASE
                            ).strip()
                            if publisher:
                                publisher = re.sub(
                                    r"(,\s+|)?((LLC|Inc|\bCo\b).*)",
                                    "",
                                    publisher,
                                    flags=re.IGNORECASE,
                                ).strip()
                                publisher = re.sub(
                                    r"[^a-zA-Z0-9\s-,\.]", "", publisher
                                ).strip()
                                publisher = titlecase(publisher)
                                write_to_file(
                                    "publishers.txt",
                                    publisher,
                                    without_timestamp=True,
                                    check_for_dup=True,
                                )
                            for c in contents:
                                if re.search(r"(Release Date:\s+)", c, re.IGNORECASE):
                                    published_date = re.sub(
                                        r"(.*:)", "", c, re.IGNORECASE
                                    ).strip()
                                    # convert March 16, 2021 to 2021-03-16
                                    year = published_date.split(",")[1].strip()
                                    month = published_date.split(" ")[0].strip()
                                    if month in [
                                        "January",
                                        "February",
                                        "March",
                                        "April",
                                        "May",
                                        "June",
                                        "July",
                                        "August",
                                        "September",
                                        "October",
                                        "November",
                                        "December",
                                    ]:
                                        month = str(
                                            list(calendar.month_name).index(month)
                                        )
                                        if len(month) == 1:
                                            month = f"0{month}"
                                    day = published_date.split(",")[0].strip()
                                    if day:
                                        day = day.split(" ")[1].strip()
                                        if len(day) == 1:
                                            day = f"0{day}"
                                    if year and month and day:
                                        published_date = f"{year}-{month}-{day}"
                                        continue
                                if re.search(r"(Language:\s+)", c, re.IGNORECASE):
                                    language = (
                                        re.sub(r"(.*:)", "", c, re.IGNORECASE)
                                        .strip()
                                        .lower()
                                    )
                                    # use langcodes to convert language to two letter code
                                    language = langcodes.find(language)
                                    if language:
                                        language = language.language
                                        continue
                                if re.search(rf"{isbn_13_regex}", c) and text_search:
                                    isbn_search = re.search(rf"{isbn_13_regex}", c)
                                    if isbn_search:
                                        isbn = isbn_search.group(1)
            else:
                print("\t\tNo bookitem-secondary-metadata found.")
        else:
            print(f"\t\tNo result found using {website_url}")
            return None
        if isbn == 0:
            isbn = ""
        provider = [x for x in providers if x.name == "kobo"]
        if provider:
            provider = provider[0]
        # return book object
        book = Book(
            isbn,
            title,
            series_name,
            volume_number,
            volume_number,
            summary,
            published_date,
            year,
            month,
            day,
            writer,
            publisher,
            "",
            categories,
            language,
            website_url,
            [image_link],
            part,
            "",
            rating,
            True,
            website_url,
            "",
            "FOR_SALE",
            provider,
            status=None,
            volume_count=0,
        )
        return book
    except Exception as e:
        send_message(f"Error getting kobo books meta: {e}", error=True)
        return None
    return None


def text_search_kobo(query):
    # html format the query with urllib.request
    query = urllib.parse.quote(query)
    search_url = f"https://www.kobo.com/us/en/search?query={query}"
    options = [
        "--disable-blink-features=AutomationControlled",
        "--window-size=7680,4320",
        "--start-maximized",
        "--headless",
        "--disable-gpu",
        "--no-sandbox",
        "--disable-dev-shm-usage",
        "user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
        "accept-language=en-US,en;q=0.9",
    ]
    driver = get_page_driver(search_url, options)
    if not driver:
        return []

    soup = BeautifulSoup(driver.page_source, "lxml")

    # filter by result-items
    soup = soup.find(
        "div",
        {
            "data-testid": "search-results-items",
            "role": "list",
            "class": "flex flex-col gap-medium",
        },
    )

    results = []
    if soup:
        # find all the hrefs in the soup
        hrefs = soup.find_all("a", href=True)
        if hrefs:
            # filter the hrefs to only include the ones that have "/us/en/ebook/" in them
            for href in hrefs:
                url = href["href"]
                if (
                    "/us/en/ebook/" in url
                    and "/us/en/ebook/series" not in url
                    and url not in results
                ):
                    results.append(url)
            if not results:
                print("\t\t - No results found")
        else:
            print("\t\t - No hrefs found")
    else:
        print("\t\t - No soup found")
    return results


# Does a text search on bookwalker, allows filtering by manga or light novels.
# Also allows limiting how many results you want returned.
def text_search_bookwalker(query, category=None, limit=None):
    base_url = "https://global.bookwalker.jp/search/?word="
    query = urllib.parse.quote(query)
    search_url = f"{base_url}{query}"

    if category == "l":
        search_url += "&qcat=3"
    elif category == "m":
        search_url += "&qcat=2"

    print(f"\tSearch URL: {search_url}")
    soup = scrape_url(
        search_url,
        SoupStrainer("ul", {"class": "o-tile-list"}),
        {
            "user-agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/86.0.4240.111 Safari/537.36",
        },
        cookies={"glSafeSearch": "1", "safeSearch": "111"},
    )
    results = []
    if soup:
        li_items = soup.find_all("li")
        if li_items:
            for li in li_items:
                # find the href from  <a class="a-tile-thumb-img"
                a_title_thumb_img = li.find("a", {"class": "a-tile-thumb-img"})
                if a_title_thumb_img:
                    # get href from a_title_thumb_img
                    href = a_title_thumb_img["href"]
                    if href:
                        if not limit:
                            results.append(href)
                        elif limit and len(results) < limit:
                            results.append(href)
                    else:
                        print("\t\t - No href found for a_title_thumb_img")
        else:
            print(f"\t\t - No results found for: {query}")
    else:
        print("\t\t - No soup found")
    return results


def get_bookwalker_books_meta(link):
    try:
        volume_number = ""
        part = ""
        series_name = ""
        image_link = ""
        rating = ""
        genres = []
        original_title = ""
        title = ""
        writer = ""
        original_worker = ""
        artist = ""
        character_designer = ""
        series_link = ""
        summary = ""
        published_date = ""
        year = ""
        month = ""
        day = ""
        language = ""
        publisher = ""
        page_count = ""
        maturity_rating = ""

        print(f"\t\t{link}")
        soup = scrape_url(
            link,
            # SoupStrainer("div", {"class": "wrap clearfix"}),
            headers={
                "user-agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/86.0.4240.111 Safari/537.36",
            },
        )
        if soup:
            # Finding high resolution preview image
            # Find <meta property="og:image" and get the content
            meta_og_image = soup.find("meta", {"property": "og:image"})
            if meta_og_image:
                if meta_og_image["content"]:
                    meta_og_image_content = meta_og_image["content"]
                    if meta_og_image_content.startswith("http"):
                        image_link = meta_og_image_content
                        if "ogp-mature" in image_link:
                            image_link = ""

            # filter it by "div", {"class": "wrap clearfix"
            soup = soup.find("div", {"class": "wrap clearfix"})
            if not soup:
                print("\t\t\t - No soup wrap clearfix found")
                return
            series_link = link
            # finding title
            h1_itemprop_name = soup.find("h1", {"itemprop": "name"})
            if h1_itemprop_name:
                title = h1_itemprop_name.text.strip()
                title = re.sub(r"(\s+-\s+(Manga|Light Novels?))$", "", title)
                original_title = title
            else:
                print("\t\t\t - No title found")
            # finding volume number
            if title and volume_number == "":
                volume_search = re.search(
                    r"([0-9]+(\.?[0-9]+)?([-_][0-9]+\.?[0-9]+)?)$",
                    title,
                )
                if volume_search:
                    volume_number = volume_search.group(1)
                    if re.search(r"-", volume_number):
                        volume_number = get_min_and_max_numbers(volume_number)
                    else:
                        volume_number = set_num_as_float_or_int(volume_number)
                elif (
                    not contains_volume_keywords(title)
                    and not contains_chapter_keywords(title)
                    and not re.search(r"([0-9]+)", title)
                ):
                    volume_number = 1
            if not part:
                part_search = get_file_part(title)
                if part_search:
                    part = part_search
            if title and volume_number == "" and not part:
                title = ""

            # finding image_link
            # Backup method for lower resolution preview image
            if not image_link:
                div_book_img = soup.find("div", {"class": "book-img"})
                if div_book_img:
                    # find <img src in div_book_img
                    img_src = div_book_img.find("img")
                    if img_src:
                        image_link = img_src["src"]
                    else:
                        print("\t\t\t - No image_link found")
                else:
                    print("\t\t\t - No div_book_img found")

            # finding summary
            div_itemprop_description = soup.find("div", {"itemprop": "description"})
            if div_itemprop_description:
                # find all <p> in div_itemprop_description
                p_items = div_itemprop_description.find_all("p")
                if p_items:
                    if len(p_items) > 1:
                        for p_item in p_items:
                            # to avoid advertisement, advertisements tend to be
                            # the synopsis-lead
                            if (
                                p_item.has_attr("class")
                                and p_item["class"][0] != "synopsis-lead"
                            ):
                                if p_item.text.strip():
                                    summary += f"{p_item.text.strip()}\n"
                    else:
                        summary = p_items[0].text.strip()
                else:
                    print("\t\t\t - No summary found")
            else:
                print("\t\t\t - No div_itemprop_description found")
            if summary:
                summary = unidecode(summary)
                # use langdetect to detect language of summary and set language with a two letter code
                try:
                    detected_lang = detect(summary)
                    if detected_lang:
                        language = detected_lang
                    else:
                        print("\t\t\t - Language detection failed")
                        print("\t\t\t - No language found")
                except Exception as e:
                    print(f"\t\t\t - Language detection failed: {e}")
                    print("\t\t\t - No language found")

                # attempting to extract title from summary
                summary_without_new_lines = remove_dual_space(
                    re.sub(r"\n", " ", summary)
                )
                extracted_title = get_title_from_description(summary_without_new_lines)
                volume_keyword = ""
                if isinstance(volume_number, list):
                    volume_keyword = "Volumes "
                else:
                    volume_keyword = "Volume "
                if extracted_title:
                    title = titlecase(extracted_title.strip())
                elif volume_number != "" and part:
                    if isinstance(volume_number, list):
                        title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume_number)} Part {part}"
                    else:
                        title = f"{volume_keyword}{volume_number} Part {part}"
                elif volume_number != "" and not part:
                    if isinstance(volume_number, list):
                        title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume_number)}"
                    else:
                        title = f"{volume_keyword}{volume_number}"

            # finding, series, author, original_worker, artist, character_designer, publisher, genres, published_date, and page_count
            div_product_detail_area = soup.find("div", {"class": "product-detail-area"})
            if div_product_detail_area:
                # find <table class="product-detail"
                table_product_detail = div_product_detail_area.find(
                    "table", {"class": "product-detail"}
                )
                if table_product_detail:
                    # find all <tr> in table_product_detail
                    tr_items = table_product_detail.find_all("tr")
                    if tr_items:
                        for tr_item in tr_items:
                            th_item = tr_item.find("th")
                            if th_item:
                                th_item_text = th_item.text.strip()
                                if re.search(
                                    r"Series Title", th_item_text, re.IGNORECASE
                                ):
                                    td_item = tr_item.find("td")
                                    if td_item:
                                        td_item_text = td_item.text.strip()
                                        if td_item_text:
                                            series_name = re.sub(
                                                r"(\s+(Manga|Light Novels?))$",
                                                "",
                                                td_item_text,
                                            )
                                            if series_name:
                                                series_name = remove_brackets(
                                                    series_name
                                                )
                                        else:
                                            print("\t\t\t - No series_name found")
                                    else:
                                        print("\t\t\t - No td_item found")
                                elif re.search(r"Author", th_item_text, re.IGNORECASE):
                                    td_item = tr_item.find("td")
                                    if td_item:
                                        td_item_text = td_item.text.strip()
                                        if td_item_text:
                                            writer = titlecase(td_item_text)
                                        else:
                                            print("\t\t\t - No author found")
                                    else:
                                        print("\t\t\t - No td_item found")
                                elif re.search(
                                    r"Original Work", th_item_text, re.IGNORECASE
                                ):
                                    td_item = tr_item.find("td")
                                    if td_item:
                                        td_item_text = td_item.text.strip()
                                        if td_item_text:
                                            original_worker = titlecase(td_item_text)
                                        else:
                                            print(
                                                "\t\t\t - No original work source found"
                                            )
                                    else:
                                        print("\t\t\t - No td_item found")
                                elif re.search(r"Artist", th_item_text, re.IGNORECASE):
                                    td_item = tr_item.find("td")
                                    if td_item:
                                        td_item_text = td_item.text.strip()
                                        if td_item_text:
                                            artist = titlecase(td_item_text)
                                        else:
                                            print("\t\t\t - No artist found")
                                    else:
                                        print("\t\t\t - No td_item found")
                                elif re.search(
                                    r"Character Design", th_item_text, re.IGNORECASE
                                ):
                                    td_item = tr_item.find("td")
                                    if td_item:
                                        td_item_text = td_item.text.strip()
                                        if td_item_text:
                                            character_designer = titlecase(td_item_text)
                                        else:
                                            print(
                                                "\t\t\t - No character designer found"
                                            )
                                    else:
                                        print("\t\t\t - No td_item found")
                                elif re.search(
                                    r"Publisher", th_item_text, re.IGNORECASE
                                ):
                                    td_item = tr_item.find("td")
                                    if td_item:
                                        td_item_text = td_item.text.strip()
                                        if td_item_text:
                                            publisher = td_item_text
                                            publisher = re.sub(
                                                r"(,\s+|)?((LLC|Inc|\bCo\b).*)",
                                                "",
                                                publisher,
                                                flags=re.IGNORECASE,
                                            ).strip()
                                            publisher = re.sub(
                                                r"[^a-zA-Z0-9\s-,\.]", "", publisher
                                            ).strip()
                                            publisher = titlecase(publisher)
                                        else:
                                            print("\t\t\t - No publisher found")
                                    else:
                                        print("\t\t\t - No td_item found")
                                elif re.search(r"Genre", th_item_text, re.IGNORECASE):
                                    td_item = tr_item.find("td")
                                    if td_item:
                                        td_item_text = td_item.text.strip()
                                        # remove all formatting through regex
                                        td_item_text = re.sub(r"\s+", " ", td_item_text)
                                        td_item_text_items = []
                                        if re.search(r",", td_item_text):
                                            # split on comma
                                            td_item_text_items = td_item_text.split(",")
                                            td_item_text_items = [
                                                td_item_text_item.strip()
                                                for td_item_text_item in td_item_text_items
                                            ]
                                        else:
                                            td_item_text_items.append(td_item_text)
                                        if td_item_text_items:
                                            genres = td_item_text_items
                                            if genres and (
                                                "Mature" in genres or "mature" in genres
                                            ):
                                                maturity_rating = "MATURE"
                                        else:
                                            print("\t\t\t - No genres found")
                                    else:
                                        print("\t\t\t - No td_item found")
                                elif re.search(
                                    r"Available since", th_item_text, re.IGNORECASE
                                ):
                                    td_item = tr_item.find("td")
                                    date = None
                                    if td_item:
                                        td_item_text = td_item.text.strip()
                                        if re.search(r"(\/)", td_item_text):
                                            # split on slash
                                            td_item_text_items = td_item_text.split("/")
                                            td_item_text_items = [
                                                td_item_text_item.strip()
                                                for td_item_text_item in td_item_text_items
                                            ]
                                            date = td_item_text_items[0]
                                        else:
                                            date = td_item_text
                                    else:
                                        print("\t\t\t - No td_item found")
                                    if date and re.search(
                                        r"(\(\d\d\:\d\d.*\).*)$", date
                                    ):
                                        # remove the time and time zone from date
                                        timeless_date = re.sub(
                                            r"(\(\d\d\:\d\d.*\).*)$", "", date
                                        ).strip()
                                        if timeless_date:
                                            # convert date to xxxx-xx-xx format
                                            converted_date = convert_date_to_yyyy_mm_dd(
                                                timeless_date
                                            )
                                            if converted_date:
                                                published_date = converted_date["date"]
                                                year = converted_date["year"]
                                                month = converted_date["month"]
                                                day = converted_date["day"]
                                            else:
                                                print(
                                                    "\t\t\t - No converted_date found"
                                                )
                                    else:
                                        print("\t\t\t - No date found")
                                elif re.search(
                                    r"Page count", th_item_text, re.IGNORECASE
                                ):
                                    td_item = tr_item.find("td")
                                    if td_item:
                                        td_item_text = td_item.text.strip()
                                        if td_item_text:
                                            page_search = re.search(
                                                r"(\d+(pages))",
                                                td_item_text,
                                                re.IGNORECASE,
                                            )
                                            if page_search:
                                                page_search = page_search.group(1)
                                                page_search_no_text = re.sub(
                                                    r"pages",
                                                    "",
                                                    page_search,
                                                    re.IGNORECASE,
                                                ).strip()
                                                page_search_no_text = (
                                                    set_num_as_float_or_int(
                                                        page_search_no_text
                                                    )
                                                )
                                                if page_search_no_text != 0:
                                                    page_count = page_search_no_text
                                                else:
                                                    print(
                                                        "\t\t\t - Page count is zero (probably a pre-order)"
                                                    )
                                            else:
                                                print("\t\t\t - No page_count found")
                                        else:
                                            print("\t\t\t - No page_count found")
                                    else:
                                        print("\t\t\t - No td_item found")
                            else:
                                print("\t\t\t - No th_item found")
                        if original_title and not series_name:
                            series_name = original_title
                    else:
                        print("\t\t\t - No tr_items found")
                        return None
                else:
                    print("\t\t\t - No table_product_detail found")
                    return None
            else:
                print("\t\t\t - No div_product_detail_area found")
                return None
        else:
            print("\t\t\t - No soup found with div class wrap clearfix")
            return None
    except Exception as e:
        print(f"Error: {e}")
        return None

    provider = [x for x in providers if x.name == "bookwalker"]
    if provider:
        provider = provider[0]
    book = Book(
        "",
        title,
        series_name,
        volume_number,
        volume_number,
        summary,
        published_date,
        year,
        month,
        day,
        writer,
        publisher,
        page_count,
        genres,
        language,
        series_link,
        [image_link],
        part,
        "",
        rating,
        True,
        series_link,
        maturity_rating,
        "FOR_SALE",
        provider,
        status=None,
        volume_count=0,
    )
    return book


def get_barnes_and_noble_books_meta(link, skip=False, data=None):
    try:
        volume_number = ""
        part = ""
        series_name = ""
        image_link = ""
        rating = ""
        title = ""
        writer = []
        summary = ""
        published_date = ""
        year = ""
        month = ""
        day = ""
        publisher = ""
        page_count = ""
        maturity_rating = ""
        isbn = ""
        is_ebook = False
        for_sale = ""
        language = ""
        soup = ""

        print(f"\t{link}")

        if not skip:
            options = [
                "--disable-blink-features=AutomationControlled",
                "--window-size=7680,4320",
                "--start-maximized",
                "--headless",
                "--disable-gpu",
                "--no-sandbox",
                "--disable-dev-shm-usage",
                "user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
                "accept-language=en-US,en;q=0.9",
            ]
            driver = get_page_driver(link, options)
            if not driver:
                return None

            soup = BeautifulSoup(driver.page_source, "lxml")

            # filter by div id "pdp-page-container"
            soup = soup.find("div", {"id": "pdp-page-container"})
        else:
            soup = data

        if soup:
            # finding title, writer, rating, and image link
            product_detail = soup.find("div", {"id": "productDetail-container"})
            if product_detail:
                # find div id="pdp-header-info"
                pdp_header_info = product_detail.find("div", {"id": "pdp-header-info"})
                if pdp_header_info:
                    # find the first h1 in the pdp-header-info
                    title_search = pdp_header_info.find("h1")
                    if title_search:
                        title = title_search.text.strip()
                        if not part:
                            part_search = get_file_part(title)
                            if part_search:
                                part = part_search
                                part = set_num_as_float_or_int(part)
                    else:
                        print("\t\t - No title found!")
                    if title and volume_number == "":
                        volume_search = re.search(
                            r"([0-9]+(\.?[0-9]+)?([-_][0-9]+\.?[0-9]+)?)$",
                            title,
                        )
                        if volume_search:
                            volume_number = volume_search.group(1)
                            if re.search(r"-", volume_number):
                                volume_number = get_min_and_max_numbers(volume_number)
                            else:
                                volume_number = set_num_as_float_or_int(volume_number)
                        elif (
                            not contains_volume_keywords(title)
                            and not contains_chapter_keywords(title)
                            and not re.search(r"([0-9]+)", title)
                        ):
                            volume_number = 1
                    if not part:
                        part_search = get_file_part(title)
                        if part_search:
                            part = part_search
                    if title and volume_number == "" and not part:
                        title = ""
                    # find span id="key-contributors"
                    key_contributors = pdp_header_info.find(
                        "span", {"id": "key-contributors"}
                    )
                    # split on ,
                    if key_contributors:
                        # get each <a href from key_contributors
                        for contributor in key_contributors.find_all(
                            "a", {"href": True}
                        ):
                            contributor_name = contributor.text.strip()
                            if contributor_name:
                                writer.append(
                                    titlecase(remove_brackets(contributor_name))
                                )
                            else:
                                print("\t\t - No contributor name found!")
                        if writer and len(writer) > 1:
                            writer = list_to_string(writer)
                        elif writer and len(writer) == 1:
                            writer = writer[0]
                    else:
                        print("\t\t - No key contributors found!")
                    # find div id="pdp-header-gigiya-wrapper"
                    # pdp_header_gigiya_wrapper = pdp_header_info.find("div", {"id": "pdp-header-gigiya-wrapper"})
                    # if pdp_header_gigiya_wrapper:
                    #     # find div itemprop="ratingValue"
                    #     rating_search = pdp_header_gigiya_wrapper.find("div", {"itemprop": "ratingValue"})
                    #     if rating_search:
                    #         rating = rating_search.text.strip()
                    #         rating = set_num_as_float_or_int(rating)
                    #         if rating == 0:
                    #             rating = ""
                    #     else:
                    #         print("\t\t - No rating found!")
                else:
                    print("\t\t - No pdp-header-info found!")
            else:
                print("\t\t - No productDetail-container found!")
                return None
            # finding summary
            # find <div class="overview-cntnt" itemprop="description">
            overview_cntnt = soup.find(
                "div", {"class": "overview-cntnt", "itemprop": "description"}
            )
            if overview_cntnt:
                # parse contents of overview_cntnt
                for content in overview_cntnt.contents:
                    # if content is not <b>
                    if content.name != "b":
                        content_text = content.text.strip()
                        if content_text:
                            summary += f"{content_text} "
                summary = summary.strip()
                # detect langauge of summary
                if summary:
                    summary = unidecode(summary)
                    language_summary_detect_attempt = detect_language(summary)
                    if language_summary_detect_attempt:
                        language = language_summary_detect_attempt
                extracted_title = get_title_from_description(summary)
                volume_keyword = ""
                if isinstance(volume_number, list):
                    volume_keyword = "Volumes "
                else:
                    volume_keyword = "Volume "
                if extracted_title:
                    title = titlecase(extracted_title.strip())
                elif volume_number != "" and part:
                    if isinstance(volume_number, list):
                        title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume_number)} Part {part}"
                    else:
                        title = f"{volume_keyword}{volume_number} Part {part}"
                elif volume_number != "" and not part:
                    if isinstance(volume_number, list):
                        title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume_number)}"
                    else:
                        title = f"{volume_keyword}{volume_number}"
            else:
                print("\t\t - No overview-cntnt found!")
            # finding image_link
            # find <img id="pdpMainImage"
            pdp_main_image = soup.find("img", {"id": "pdpMainImage"})
            if pdp_main_image:
                image_link = pdp_main_image["src"]
                # remove // from beginning of image_link
                image_link = re.sub(r"^(//)", "https://", image_link)
            else:
                print("\t\t - No pdpMainImage found!")
            # finding isbn, publisher, published date, series, volume_number, and page count
            # find <table class="plain centered">
            plain_centered = soup.find("table", {"class": "plain centered"})
            if plain_centered:
                tr_items = plain_centered.find_all("tr")
                if tr_items:
                    for tr in tr_items:
                        th_item = tr.find("th")
                        td_item = tr.find("td")
                        if th_item and td_item:
                            th_item = th_item.text.strip()
                            td_item = td_item.text.strip()
                            if re.search(r"isbn", th_item, re.IGNORECASE):
                                if not isbn:
                                    isbn_search = re.search(
                                        rf"({isbn_13_regex})", td_item
                                    )
                                    if isbn_search:
                                        isbn = isbn_search.group(1)
                                    else:
                                        print("\t\t - No ISBN found with regex!")
                            elif re.search(r"publisher", th_item, re.IGNORECASE):
                                publisher = td_item
                                publisher = re.sub(
                                    r"(,\s+|)?((LLC|Inc|\bCo\b).*)",
                                    "",
                                    publisher,
                                    flags=re.IGNORECASE,
                                ).strip()
                                publisher = re.sub(
                                    r"[^a-zA-Z0-9\s-,\.]", "", publisher
                                ).strip()
                                publisher = titlecase(publisher)
                            elif re.search(r"publication date", th_item, re.IGNORECASE):
                                published_date = td_item
                                # convert published date from mm/dd/yyyy to yyyy-mm-dd
                                published_date = re.sub(
                                    r"(\d{2})/(\d{2})/(\d{4})",
                                    r"\3-\1-\2",
                                    published_date,
                                )
                                if published_date:
                                    year, month, day = published_date.split("-")
                                else:
                                    print("\t\t - No published date found!")
                            elif re.search(r"series", th_item, re.IGNORECASE):
                                if re.search(r",", td_item):
                                    if not series_name:
                                        series_name = td_item.split(",")[0].strip()
                                        series_name = remove_brackets(series_name)
                                        if not part:
                                            part_search = get_file_part(series_name)
                                            if part_search:
                                                part = part_search
                                                part = set_num_as_float_or_int(part)
                                    if volume_number == "":
                                        volume_number_search = td_item.split(",")[
                                            1
                                        ].strip()
                                        if re.search(r"#", volume_number_search):
                                            volume_number_search = re.sub(
                                                r"#", "", volume_number_search
                                            )
                                            volume_number = set_num_as_float_or_int(
                                                volume_number_search
                                            )
                                else:
                                    if not series_name:
                                        series_name = td_item
                            elif re.search(r"format", th_item, re.IGNORECASE):
                                format = td_item
                                if re.search(r"ebook|nook", format, re.IGNORECASE):
                                    is_ebook = True
                                    for_sale = "FOR_SALE"
                                else:
                                    is_ebook = False
                            elif re.search(r"pages", th_item, re.IGNORECASE):
                                page_count = td_item
                                if page_count.isdigit():
                                    page_count = set_num_as_float_or_int(page_count)
                                    if page_count == 0:
                                        page_count = ""
                                else:
                                    print("\t\t - No page count found!")
                        else:
                            print("\t\t - No th or td found!")
                else:
                    print("\t\t - No tr items found!")
            else:
                print("\t\t - No plain centered found!")
                return None
        else:
            print("\t\t - No soup found!")
            return None
    # create book object and return it
    except Exception as e:
        send_message(f"Error getting barnes and noble books meta: {e}", error=True)
        return None

    provider = [x for x in providers if x.name == "barnes_and_noble"]
    if provider:
        provider = provider[0]
    book = Book(
        isbn,
        title,
        series_name,
        volume_number,
        volume_number,
        summary,
        published_date,
        year,
        month,
        day,
        writer,
        publisher,
        page_count,
        "",
        language,
        link,
        [image_link],
        part,
        "",
        "",
        is_ebook,
        link,
        "",
        for_sale,
        provider,
        status=None,
        volume_count=0,
    )
    return book


def text_search_barnes_and_noble(query):
    base_url = "https://www.barnesandnoble.com/s/"
    query = urllib.parse.quote(query)
    search_url = f"{base_url}{query}/_/N-8qa"

    options = [
        "--disable-blink-features=AutomationControlled",
        "--window-size=7680,4320",
        "--start-maximized",
        "--headless",
        "--disable-gpu",
        "--no-sandbox",
        "--disable-dev-shm-usage",
        "user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
        "accept-language=en-US,en;q=0.9",
    ]
    driver = get_page_driver(search_url, options)
    if not driver:
        return []

    soup = BeautifulSoup(driver.page_source, "lxml")

    # filter by result-items
    # soup = soup.find("div", {"class": "product-shelf-grid plp-grid-qa"})

    clean_results = []
    if soup:
        # find all div class="product-shelf-title product-info-title pt-xs"
        results = soup.find_all(
            "div", {"class": "product-shelf-title product-info-title pt-xs"}
        )
        if results:
            for result in results:
                title = result.find("a", {"title": True})
                if title:
                    href = title["href"]
                    if href:
                        link = f"https://www.barnesandnoble.com{href}"
                        if link not in clean_results:
                            clean_results.append(link)
                    else:
                        print(f"No link found for: {title}")
                else:
                    print(f"No title found for: {result}")
        else:
            second_soup = soup.find("div", {"id": "pdp-page-container"})
            if second_soup and second_soup.contents:
                # get full_url from second_soup
                return get_barnes_and_noble_books_meta(
                    search_url, skip=True, data=second_soup
                )
            print(f"No results found for: {query}")
    else:
        print("No soup found!")
    return clean_results


def search_comic_vine(query, api_key, limit=None):
    books = []
    try:
        session = Comicvine(api_key=api_key, cache=None)
        results = session.search(
            resource=ComicvineResource.ISSUE, query=query, max_results=15
        )
        if results:
            for result in results:
                try:
                    isbn = ""
                    api_url = ""
                    summary = ""
                    image_link = ""
                    issue_id = ""
                    volume_number = ""
                    part = ""
                    preview_link = ""
                    series_name = ""
                    published_date = ""
                    year = ""
                    month = ""
                    day = ""
                    title = ""
                    name = ""
                    writer = ""
                    publisher = ""
                    page_count = ""
                    language = ""
                    categories = []
                    average_rating = ""
                    is_ebook = True
                    maturity_rating = ""
                    series_id = ""
                    store_availability_status = "FOR_SALE"
                    provider = [x for x in providers if x.name == "comic_vine"]
                    genres = []
                    tags = []

                    if hasattr(result, "site_url"):
                        preview_link = result.site_url
                        if preview_link:
                            print(f"\tLink: {preview_link}")
                    else:
                        print("\t\t\t - No site_url")
                    if hasattr(result, "name"):
                        name = result.name
                    if hasattr(result, "api_url"):
                        api_url = result.api_url
                    else:
                        print("\t\t\t - No api_url")

                    if hasattr(result, "description"):
                        summary_search = result.description
                        if summary_search:
                            # unescape the summary
                            summary_search = html.unescape(summary_search)
                            # remove all html tags from the summary
                            summary_search = re.sub(r"<[^>]*>", " ", summary_search)
                            summary_search = re.sub(
                                r"(Contents([-_. ]+)?(Chapter)?.*)", "", summary_search
                            )
                            summary_search = remove_dual_space(summary_search).strip()
                            if re.search(
                                r"(^(Chapter([-_. ]+)?Titles.*)|(Chapter([-_. ]+)?Titles.*)$)",
                                summary_search,
                                re.IGNORECASE,
                            ):
                                summary_search = re.sub(
                                    r"(^(Chapter([-_. ]+)?Titles.*)|(Chapter([-_. ]+)?Titles.*)$)",
                                    "",
                                    summary_search,
                                    flags=re.IGNORECASE,
                                )
                            summary_search = remove_dual_space(summary_search).strip()
                            if summary_search and len(summary_search) >= 3:
                                summary = summary_search
                    else:
                        print("\t\t\t - No description")
                    if hasattr(result, "image"):
                        if hasattr(result.image, "original_url"):
                            image_link = result.image.original_url
                        else:
                            print("\t\t\t - No original image inside of image_url")
                    else:
                        print("\t\t\t - No image")
                    if hasattr(result, "id"):
                        issue_id = result.id
                        if issue_id:
                            print(f"\t\tIssue ID: {issue_id}")
                    else:
                        print("\t\t\t - No id")
                    if hasattr(result, "volume"):
                        if hasattr(result.volume, "name"):
                            series_name = result.volume.name
                        else:
                            print("\t\t\t - No name inside of volume")
                    if hasattr(result, "number"):
                        volume_number_search = result.number
                        if volume_number_search:
                            if re.search(r"-", volume_number_search):
                                volume_number = get_min_and_max_numbers(
                                    volume_number_search
                                )
                            else:
                                volume_number = set_num_as_float_or_int(
                                    volume_number_search
                                )
                    else:
                        print("\t\t\t - No volume number")
                    if hasattr(result, "store_date"):
                        published_date = result.store_date
                        if published_date:
                            year = published_date.year
                            month = published_date.month
                            day = published_date.day
                            published_date = f"{year}-{month}-{day}"

                            if re.search(r"(-+$)", published_date):
                                published_date = re.sub(
                                    r"(-+$)", "", published_date
                                ).strip()
                        else:
                            published_date = ""
                    else:
                        print("\t\t\t - No store_date")
                    if name and volume_number == "":
                        volume_search = re.search(
                            r"([0-9]+(\.?[0-9]+)?([-_][0-9]+\.?[0-9]+)?)$",
                            name,
                        )
                        if volume_search:
                            volume_number = volume_search.group(1)
                            if re.search(r"-", volume_number):
                                volume_number = get_min_and_max_numbers(volume_number)
                            else:
                                volume_number = set_num_as_float_or_int(volume_number)
                        elif (
                            not contains_volume_keywords(name)
                            and not contains_chapter_keywords(name)
                            and not re.search(r"([0-9]+)", name)
                        ):
                            volume_number = 1
                    if not part and name:
                        part_search = get_file_part(name)
                        if part_search:
                            part = part_search
                    if name and volume_number == "" and not part:
                        name = ""
                    extracted_title = ""
                    if summary:
                        summary = unidecode(summary)
                        extracted_title = get_title_from_description(summary)
                    volume_keyword = ""
                    if isinstance(volume_number, list):
                        volume_keyword = "Volumes "
                    else:
                        volume_keyword = "Volume "
                    if extracted_title:
                        title = titlecase(extracted_title.strip())
                    elif volume_number != "" and part:
                        if isinstance(volume_number, list):
                            title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume_number)} Part {part}"
                        else:
                            title = f"{volume_keyword}{volume_number} Part {part}"
                    elif volume_number != "" and not part:
                        if isinstance(volume_number, list):
                            title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume_number)}"
                        else:
                            title = f"{volume_keyword}{volume_number}"
                    if not language and summary:
                        language = detect_language(summary)
                    provider = [x for x in providers if x.name == "comic_vine"]
                    if provider:
                        provider = provider[0]
                    book = Book(
                        isbn,
                        title,
                        series_name,
                        volume_number,
                        volume_number,
                        summary,
                        published_date,
                        year,
                        month,
                        day,
                        writer,
                        publisher,
                        page_count,
                        categories,
                        language,
                        preview_link,
                        [image_link],
                        part,
                        series_id,
                        average_rating,
                        is_ebook,
                        preview_link,
                        maturity_rating,
                        store_availability_status,
                        provider,
                        None,
                        0,
                        genres,
                        tags,
                    )
                    books.append(book)
                    if limit and len(books) == limit:
                        break
                except Exception as e:
                    id_to_send = result.id if hasattr(result, "id") else issue_id
                    send_message(
                        f"\tComic Vine Issue ID: {id_to_send}: {e}", error=True
                    )
                    write_to_file("comic_vine_errors.txt", str(e))
        else:
            print("\t\t\t - No results found!")
    except Exception as e:
        send_message(str(e), error=True)
        write_to_file("comic_vine_errors.txt", str(e))
    return books


# Credit to original source: https://alamot.github.io/epub_cover/
# Modified by me.
# Retrieves the inner novel cover
def get_novel_cover(novel_path):
    namespaces = {
        "calibre": "http://calibre.kovidgoyal.net/2009/metadata",
        "dc": "http://purl.org/dc/elements/1.1/",
        "dcterms": "http://purl.org/dc/terms/",
        "opf": "http://www.idpf.org/2007/opf",
        "u": "urn:oasis:names:tc:opendocument:xmlns:container",
        "xsi": "http://www.w3.org/2001/XMLSchema-instance",
    }

    try:
        with zipfile.ZipFile(novel_path) as z:
            t = etree.fromstring(z.read("META-INF/container.xml"))
            rootfile_path = t.xpath(
                "/u:container/u:rootfiles/u:rootfile", namespaces=namespaces
            )
            if rootfile_path:
                rootfile_path = rootfile_path[0].get("full-path")
                t = etree.fromstring(z.read(rootfile_path))
                cover_id = t.xpath(
                    "//opf:metadata/opf:meta[@name='cover']", namespaces=namespaces
                )
                if cover_id:
                    cover_id = cover_id[0].get("content")
                    cover_href = t.xpath(
                        f"//opf:manifest/opf:item[@id='{cover_id}']",
                        namespaces=namespaces,
                    )
                    if cover_href:
                        cover_href = cover_href[0].get("href")
                        if "%" in cover_href:
                            cover_href = urllib.parse.unquote(cover_href)
                        cover_path = os.path.join(
                            os.path.dirname(rootfile_path), cover_href
                        )
                        return cover_path
                    else:
                        print("\t\t\tNo cover_href found in get_novel_cover()")
                else:
                    print("\t\t\tNo cover_id found in get_novel_cover()")
            else:
                print(
                    "\t\t\tNo rootfile_path found in META-INF/container.xml in get_novel_cover()"
                )
    except Exception as e:
        send_message(str(e), error=True)
    return None


# Returns the path of the cover image for a novel file, if it exists.
def get_novel_cover_path(file):
    if file.extension not in novel_extensions:
        return ""

    novel_cover_path = get_novel_cover(file.path)
    if not novel_cover_path:
        return ""

    if get_file_extension(novel_cover_path) not in image_extensions:
        return ""

    return os.path.basename(novel_cover_path)


# Compresses an image and saves it to a file or returns the compressed image data.
def compress_image(image_path, quality=60, to_jpg=False, raw_data=None):
    new_filename = None
    buffer = None
    save_format = "JPEG"

    # Load the image from the file or raw data
    image = Image.open(image_path if not raw_data else io.BytesIO(raw_data))

    # Convert the image to RGB if it has an alpha channel or uses a palette
    if image.mode in ("RGBA", "P"):
        image = image.convert("RGB")

    filename, ext = os.path.splitext(image_path)

    if ext == ".webp":
        save_format = "WEBP"

    # Determine the new filename for the compressed image
    if not raw_data:
        if to_jpg or ext.lower() == ".png":
            ext = ".jpg"
            if not to_jpg:
                to_jpg = True
        new_filename = f"{filename}{ext}"

    # Try to compress and save the image
    try:
        if not raw_data:
            image.save(new_filename, format=save_format, quality=quality, optimize=True)
        else:
            buffer = io.BytesIO()
            image.save(buffer, format=save_format, quality=quality)
            return buffer.getvalue()
    except Exception as e:
        # Log the error and continue
        send_message(f"Failed to compress image {image_path}: {e}", error=True)

    # Remove the original file if it's a PNG that was converted to JPG
    if to_jpg and ext.lower() == ".jpg" and os.path.isfile(image_path):
        os.remove(image_path)

    # Return the path to the compressed image file, or the compressed image data
    return new_filename if not raw_data else buffer.getvalue()


# Regular expressions to match cover patterns
cover_patterns = [
    r"(cover\.([A-Za-z]+))$",
    r"(\b(Cover([0-9]+|)|CoverDesign|page([-_. ]+)?cover)\b)",
    r"(\b(p000|page_000)\b)",
    r"((\s+)0+\.(.{2,}))",
    r"(\bindex[-_. ]1[-_. ]1\b)",
    r"(9([-_. :]+)?7([-_. :]+)?(8|9)(([-_. :]+)?[0-9]){10})",
]

# Pre-compiled regular expressions for cover patterns
compiled_cover_patterns = [
    re.compile(pattern, flags=re.IGNORECASE) for pattern in cover_patterns
]


# Finds and extracts the internal cover from a manga or novel file.
def find_and_extract_cover(
    file,
    return_data_only=False,
    silent=False,
):
    # Helper function to filter and sort files in the zip archive
    def filter_and_sort_files(zip_list):
        return sorted(
            [
                x
                for x in zip_list
                if not x.endswith("/")
                and "." in x
                and get_file_extension(x) in image_extensions
                and not os.path.basename(x).startswith((".", "__"))
            ]
        )

    # Helper function to read image data from the zip file
    def get_image_data(image_path):
        with zip_ref.open(image_path) as image_file_ref:
            return image_file_ref.read()

    # Helper function to save image data to a file
    def save_image_data(image_path, image_data):
        with open(image_path, "wb") as image_file_ref_out:
            image_file_ref_out.write(image_data)

    # Helper function to process a cover image and save or return the data
    def process_cover_image(cover_path, image_data=None):
        image_extension = get_file_extension(os.path.basename(cover_path))
        if image_extension == ".jpeg":
            image_extension = ".jpg"

        if output_covers_as_webp and image_extension != ".webp":
            image_extension = ".webp"

        output_path = os.path.join(file.root, file.extensionless_name + image_extension)

        if not return_data_only:
            save_image_data(output_path, image_data)
            if compress_image_option:
                result = compress_image(output_path, image_quality)
                return result if result else output_path
            return output_path
        elif image_data:
            compressed_data = compress_image(output_path, raw_data=image_data)
            return compressed_data if compressed_data else image_data
        return None

    # Check if the file exists
    if not os.path.isfile(file.path):
        send_message(f"\nFile: {file.path} does not exist.", error=True)
        return None

    # Check if the input file is a valid zip file
    if not zipfile.is_zipfile(file.path):
        send_message(f"\nFile: {file.path} is not a valid zip file.", error=True)
        return None

    # Get the novel cover path if the file has a novel extension
    novel_cover_path = (
        get_novel_cover_path(file) if file.extension in novel_extensions else ""
    )

    # Open the zip file
    with zipfile.ZipFile(file.path, "r") as zip_ref:
        # Filter and sort files in the zip archive
        zip_list = filter_and_sort_files(zip_ref.namelist())

        # Move the novel cover to the front of the list, if it exists
        if novel_cover_path:
            novel_cover_basename = os.path.basename(novel_cover_path)
            for i, item in enumerate(zip_list):
                if os.path.basename(item) == novel_cover_basename:
                    zip_list.pop(i)
                    zip_list.insert(0, item)
                    break

        # Set of blank images
        blank_images = set()

        # Iterate through the files in the zip archive
        for image_file in zip_list:
            # Check if the file matches any cover pattern
            for pattern in compiled_cover_patterns:
                image_basename = os.path.basename(image_file)
                is_novel_cover = novel_cover_path and image_basename == novel_cover_path

                if (
                    is_novel_cover
                    or pattern.pattern == image_basename
                    or pattern.search(image_basename)
                ):
                    image_data = get_image_data(image_file)
                    result = process_cover_image(image_file, image_data)
                    if result:
                        return result

        # Find a non-blank default cover
        default_cover_path = None
        for test_file in zip_list:
            if test_file in blank_images:
                continue

            image_data = get_image_data(test_file)

            # Check if the user has enabled the option to compare detected covers to blank images
            default_cover_path = test_file
            break

        # Process the default cover if found
        if default_cover_path:
            image_data = get_image_data(default_cover_path)
            result = process_cover_image(default_cover_path, image_data)
            if result:
                return result

    return False


class PossibleSubtitle:
    def __init__(self, type, text):
        self.type = type
        self.text = text


# Searches the passes metadata provider
def search_provider(volume, provider, zip_comment, dir_files=None):
    global series_ids_cache
    global cached_series_result
    global successful_match
    global image_link_cache
    global file_descriptions, result_subtitles

    session_result = []
    series_info = []
    dir_file_series_ids = []

    cover = find_cover_file(volume.path)
    internal_cover_data = None

    if use_internal_cover or not cover:
        internal_cover_data = find_and_extract_cover(volume, return_data_only=True)

    if not cover:
        print("\t\tNo external cover found.")
        if not internal_cover_data:
            if use_internal_cover:
                print("\t\tNo internal cover found.")
            else:
                print(
                    "\t\tuse_internal_cover is disabled and no external cover was found, skipping..."
                )
            return None
    else:
        print(f"\n\tExternal Cover: {os.path.basename(cover)}")
        if use_internal_cover:
            print("\n\tUsing internal cover.")

    if volume.volume_part:
        volume.volume_part = set_num_as_float_or_int(volume.volume_part)

    send_discord_message(
        None,
        "Searching Provider",
        color=8421504,
        fields=[
            {
                "name": "Name",
                "value": provider.name,
                "inline": False,
            },
        ],
    )

    if provider.name == "google-books":
        print("\tSearching folder files for a common series_id...")

        # Get a list of files in the volume's root directory
        series_files = [
            f
            for f in os.listdir(volume.root)
            if os.path.isfile(os.path.join(volume.root, f))
        ]

        multiple_series_ids = False

        if series_files:
            # Clean and sort the list of files
            clean = clean_and_sort(volume.root, series_files)
            series_files = clean[0]
            in_cache = False

            if not series_ids_cache and os.path.isfile(cached_series_temp_path):
                with open(cached_series_temp_path, "r") as f:
                    try:
                        series_ids_cache_tmp = json.load(f)
                        series_ids_cache = [
                            Series_Page_Result.from_dict(result_dict)
                            for result_dict in series_ids_cache_tmp
                        ]
                    except Exception as e:
                        send_message(str(e), error=True)
                        series_ids_cache = []

            # Check if the series is already in the cache
            if series_ids_cache and volume.series_name:
                for item in series_ids_cache:
                    if (
                        item.series_name.lower().strip()
                        == volume.series_name.lower().strip()
                    ):
                        print("\tFound series in cache!")
                        in_cache = True
                        series_info.extend(item.results)
                        session_result = item
                        break

            if not in_cache:
                # delete the temp file if it exists
                if os.path.isfile(cached_series_temp_path):
                    try:
                        os.remove(cached_series_temp_path)
                    except Exception as e:
                        send_message(str(e), error=True)

                # get all the paths for the files in the directory
                dir_file_paths = [
                    os.path.join(volume.root, x)
                    for x in series_files
                    if series_files
                    and os.path.isfile(os.path.join(volume.root, x))
                    and get_series_name_from_volume(x).lower().strip()
                    == volume.series_name.lower().strip()
                ]

                # get the zip comments
                zip_comments = [
                    get_identifiers(get_zip_comment(x)) for x in dir_file_paths if x
                ]

                # remove empty results from zip_comments
                zip_comments = [x for x in zip_comments if x]
                series_ids = []

                # only keep the series_id from the zip comments
                for comment in zip_comments:
                    for item in comment:
                        if re.search(r"series_id:.*", item, re.IGNORECASE):
                            series_ids.append(item)
                            break

                global manual_series_id_mode

                if manual_series_id_mode:
                    # ask the user for a series_id, and add it to the dir_file_series_ids list
                    user_series_id = input(
                        f"\n\tEnter a series_id for the series: {volume.series_name} (leave blank to skip):"
                    )
                    if user_series_id:
                        user_series_id = f"series_id:{user_series_id}"

                        if user_series_id not in series_ids:
                            series_ids.append(user_series_id)
                            manual_series_id_mode = False

                # remove all duplicates from dir_file_series_ids
                dir_file_series_ids = list(set(series_ids))

                if len(dir_file_series_ids) == 1:
                    dir_file_series_ids = dir_file_series_ids[0]
                elif len(dir_file_series_ids) > 1:
                    send_message(
                        f"\tSeriesIDs from zip comments is greater than 1: {dir_file_series_ids}"
                    )
                    multiple_series_ids = True

                if dir_file_series_ids:
                    # Extract series_id from the input
                    dir_file_series_ids = [
                        x.split("series_id:")[1]
                        for x in series_ids
                        if x.split("series_id:")[1]
                    ]
                    # remove duplicates
                    dir_file_series_ids = list(set(dir_file_series_ids))

                    series_id_in_cache = False

                    for id in dir_file_series_ids:
                        # Check if series_id is in the cache
                        if series_ids_cache:
                            for item in series_ids_cache:
                                if item.series_id == dir_file_series_ids:
                                    print("\tFound series_id in cache!")
                                    series_id_in_cache = True
                                    series_info.extend(item.results)
                                    session_result.append(item)
                                    break
                        print(
                            f"\n\tScraping series info for: https://play.google.com/store/books/series?id={id}"
                            + "\n\t\tMay take awhile depending on the number of ids..."
                        )
                        series_info_scrapped = scrape_series_ids(id)

                        if not series_info_scrapped:
                            continue

                        series_info.extend(series_info_scrapped)

                        # Check for discrepancies between local files and online series
                        if (
                            user_mode == "path"
                            and series_info
                            and dir_files
                            and len(series_info) != len(dir_files)
                        ):
                            print(f"\n\tdir_files: {len(dir_files)}")
                            print(f"\tseries_info: {len(series_info)}")

                            if len(dir_file_series_ids) == 1:
                                if len(series_info) > len(dir_files):
                                    # inform the user that there are new volumes in the series
                                    message = (
                                        f"\n\tNew volumes found for series_id: {dir_file_series_ids} ({len(series_info)} ids found)"
                                        + f"\n\t\t https://play.google.com/store/books/series?id={dir_file_series_ids[0]}"
                                    )
                                    send_message(message)
                                    write_to_file("new_volumes_found.txt", message)
                                else:
                                    # let the user know there's a mismatch in the number of files and the number of ids found
                                    # also send the full link with the message
                                    message = (
                                        f"\n\tMore volumes in local library than online, with series_id: {dir_file_series_ids} ({len(series_info)} ids found)"
                                        + f"\n\t\t https://play.google.com/store/books/series?id={dir_file_series_ids}"
                                    )
                                    send_message(message)
                                    write_to_file(
                                        "more_volumes_in_local_library.txt", message
                                    )

                        # Display the found series info
                        if series_info_scrapped:
                            print(f"\t\t\tFound {len(series_info_scrapped)} ids:")
                            for item in series_info_scrapped:
                                # print each item with [number in array] item
                                print(
                                    f"\t\t\t\t[{series_info_scrapped.index(item) + 1}] {item}"
                                )
                        else:
                            print("\tNothing found")

                    if series_info:
                        session_result = Series_Page_Result(
                            dir_file_series_ids,
                            volume.series_name,
                            series_info,
                            [],
                        )
        else:
            print("\tNo other files found in directory for series_id search.")

    if (cover or internal_cover_data) and not skip_image_comparison:
        print(
            f"\n{'-' * 64}\nUsing string search + image comparison matching.\n{'-' * 64}"
        )

        series_id_w_matching_vol_to_ord_num = []
        cleaned_results = []

        if volume.series_name and volume.volume_number != "":
            # Define the base search string
            search_base = volume.series_name

            # Check if volume_number is a list and convert it to a string
            volume_number_search_string = (
                str(volume.volume_number[0])
                if isinstance(volume.volume_number, list)
                else str(volume.volume_number)
            )

            # Create search strings with different formats
            search = f"{search_base} Volume {volume_number_search_string}"
            search_two = f"{search_base} Vol. {volume_number_search_string}"
            search_three = search_base
            search_four = f"{search_base} Volume {volume_number_search_string}"
            search_five = f"{search_base} {volume_number_search_string}"

            # The arrays to hold each searches' results
            clean_r_results = []
            clean_b_results = []
            clean_no_volume_keyword_results = []
            clean_no_volume_keyword_results_newest = []
            clean_no_volume_keyword_results_no_cat = []

            # Check if volume_part exists and add it to the search strings
            if volume.volume_part:
                volume.volume_part = set_num_as_float_or_int(volume.volume_part)
                part_string = f" Part {volume.volume_part}"
                search += part_string
                search_two += part_string
                search_four += part_string

            # Check the extension and update the search string accordingly
            search += " Light Novel" if volume.extension == ".epub" else " Manga"

            print(f"\nSearching with: {search}")
            if cover and not use_internal_cover:
                print(f"Cover Image: {os.path.basename(cover)}")

            print(f"Required Image SSIM Score: {required_image_ssim_score}")

            first_word_in_series = remove_punctuation(volume.series_name).split(" ")[0]

            if provider.name == "google-books":
                if series_info and (
                    not session_result or not session_result.api_results
                ):
                    series_info = list(dict.fromkeys(series_info))
                    print("\nSearching with all folder series ids")
                    series_search_results = []
                    print(f"Total series results: {len(series_info)}")

                    for index, id in enumerate(series_info, start=1):
                        if id in series_info:
                            print(
                                f"\t[{index}] https://www.googleapis.com/books/v1/volumes/{id}"
                            )

                        series_search = search_google_books(
                            0,
                            volume.path,
                            volume_id=id,
                            max_results_num=40,
                            mute_output=True,
                        )
                        time.sleep(sleep_time)

                        if series_search:
                            series_search_results.append(series_search)

                    if series_search_results:
                        clean_series_search_results = clean_api_results(
                            series_search_results,
                            volume.volume_number,
                            first_word_in_series,
                            volume.multi_volume,
                            volume.series_name,
                            volume.extension,
                            volume.volume_part,
                            skip_vol_nums_equal=True,
                            skip_contains_first_word=True,
                            skip_omnibus_check=True,
                            skip_manga_keyword_check=True,
                            skip_series_similarity=True,
                            skip_isebook_check=False,
                            skip_categories_check=True,
                            skip_summary_check=False,
                        )
                        if clean_series_search_results:
                            series_subtitles = [
                                x.subtitle
                                for x in clean_series_search_results
                                if x.subtitle
                            ]
                            if series_subtitles:
                                # only keep the subtitles that have a count of 2 or more
                                series_subtitles = [
                                    x
                                    for x in series_subtitles
                                    if series_subtitles.count(x) > 1
                                ]
                            # remove duplicates
                            series_subtitles = list(dict.fromkeys(series_subtitles))

                            if series_subtitles:
                                for subtitle in series_subtitles:
                                    ps_obj = PossibleSubtitle("title", subtitle)

                                    if subtitle not in file_descriptions:
                                        file_descriptions.append(ps_obj)
                                    if subtitle not in result_subtitles:
                                        result_subtitles.append(ps_obj)

                            if session_result:
                                session_result.api_results = clean_series_search_results
                                series_ids_cache.append(session_result)

                                serialized_data = [
                                    result.to_dict() for result in series_ids_cache
                                ]

                                # Write the items in the cache to a tmp json file subsequent script runs
                                try:
                                    with open(cached_series_temp_path, "w") as f:
                                        json.dump(serialized_data, f, indent=4)
                                        print(
                                            f"\n\tWrote series_ids_cache to: {cached_series_temp_path}\n"
                                        )
                                except Exception as e:
                                    send_message(str(e), error=True)

                            for result in clean_series_search_results:
                                cleaned_results.append(result)
                                if (
                                    not multiple_series_ids
                                    and (
                                        result.series_id_order_number
                                        and volume.volume_number != ""
                                    )
                                    and (
                                        result.series_id_order_number
                                        == volume.volume_number
                                    )
                                    and result.series_id_order_number == result.volume
                                    and result
                                    not in series_id_w_matching_vol_to_ord_num
                                ):
                                    series_id_w_matching_vol_to_ord_num.append(result)
                elif session_result and session_result.api_results:
                    series_subtitles = [
                        x.subtitle for x in session_result.api_results if x.subtitle
                    ]
                    if series_subtitles:
                        # only keep the subtitles that have a count of 2 or more
                        series_subtitles = [
                            x for x in series_subtitles if series_subtitles.count(x) > 1
                        ]
                    # remove duplicates
                    series_subtitles = list(dict.fromkeys(series_subtitles))

                    if series_subtitles:
                        for subtitle in series_subtitles:
                            ps_obj = PossibleSubtitle("title", subtitle)

                            if subtitle not in file_descriptions:
                                file_descriptions.append(ps_obj)
                            if subtitle not in result_subtitles:
                                result_subtitles.append(ps_obj)

                    for result in session_result.api_results:
                        if result not in cleaned_results:
                            cleaned_results.append(result)

                        if (
                            not len(session_result.series_id) > 1
                            and (
                                result.series_id_order_number != ""
                                and volume.volume_number != ""
                            )
                            and (result.series_id_order_number == volume.volume_number)
                            and result.series_id_order_number == result.volume
                            and result not in series_id_w_matching_vol_to_ord_num
                        ):
                            series_id_w_matching_vol_to_ord_num.append(result)

            series_id_matching_vol_results = []

            if series_id_w_matching_vol_to_ord_num:
                for item in series_id_w_matching_vol_to_ord_num:
                    # get the volume_id from the end of the item.api_link
                    api_link_match = re.search(r"(\/volumes\/)", item.api_link)

                    if api_link_match:
                        volume_id = os.path.basename(item.api_link)

                        if volume_id:
                            series_id_matching_item_search = search_google_books(
                                0,
                                volume.path,
                                volume_id=volume_id,
                                max_results_num=40,
                            )

                            if len(series_id_w_matching_vol_to_ord_num) > 1:
                                time.sleep(web_scrape_sleep_time)

                            if series_id_matching_item_search:
                                series_id_matching_vol_results.append(
                                    series_id_matching_item_search
                                )

                if series_id_matching_vol_results:
                    clean_series_id_matching_vol_results = clean_api_results(
                        series_id_matching_vol_results,
                        volume.volume_number,
                        first_word_in_series,
                        volume.multi_volume,
                        volume.series_name,
                        volume.extension,
                        volume.volume_part,
                        skip_vol_nums_equal=False,
                        skip_contains_first_word=False,
                        skip_omnibus_check=True,
                        skip_manga_keyword_check=True,
                        skip_series_similarity=False,
                        skip_isebook_check=False,
                        skip_categories_check=True,
                        skip_summary_check=False,
                    )

                    if clean_series_id_matching_vol_results:
                        cleaned_results.extend(
                            [
                                result
                                for result in clean_series_id_matching_vol_results
                                if result not in cleaned_results
                            ]
                        )

                    series_id_w_matching_vol_to_ord_num = (
                        clean_series_id_matching_vol_results
                    )
            if provider.name == "google-books":
                # zip comment search
                if zip_comment:
                    print("\nChecking zip comment for isbn obtained elsewhere...")
                    isbn = isbn_search(zip_comment, volume.name)

                    if isbn:
                        print(
                            f"\tFound isbn in zip comment: {isbn.isbn}, adding to list of results."
                        )

                        clean_google_result = clean_api_results(
                            [isbn],
                            volume.volume_number,
                            first_word_in_series,
                            volume.multi_volume,
                            volume.series_name,
                            volume.extension,
                            volume.volume_part,
                            skip_series_similarity=True,
                            skip_vol_nums_equal=True,
                            skip_categories_check=True,
                        )
                        cleaned_results.extend(
                            [
                                result
                                for result in clean_google_result
                                if result not in cleaned_results
                            ]
                        )

                # search one search
                r = search_google_books(
                    0,
                    volume.path,
                    search,
                    in_line_search=False,
                    number=volume.volume_number,
                )
                if r:
                    clean_r_results = clean_api_results(
                        r,
                        volume.volume_number,
                        first_word_in_series,
                        volume.multi_volume,
                        volume.series_name,
                        volume.extension,
                        volume.volume_part,
                        skip_contains_first_word=True,
                        skip_vol_nums_equal=True,
                    )
                    cleaned_results.extend(
                        [
                            result
                            for result in clean_r_results
                            if result not in cleaned_results
                        ]
                    )

                # search one search with quotes
                if not series_info:
                    print(f"\nAdditional volume quoted search: {search}")
                    b = search_google_books(
                        0,
                        volume.path,
                        search,
                        in_line_search=False,
                        number=volume.volume_number,
                        quoted_search=True,
                    )
                    if b:
                        clean_b_results = clean_api_results(
                            b,
                            volume.volume_number,
                            first_word_in_series,
                            volume.multi_volume,
                            volume.series_name,
                            volume.extension,
                            volume.volume_part,
                            skip_contains_first_word=True,
                            skip_vol_nums_equal=True,
                        )
                        cleaned_results.extend(
                            [
                                result
                                for result in clean_b_results
                                if result not in cleaned_results
                            ]
                        )

                    # search without volume keyword
                    if not series_info:
                        print(
                            f"\nAdditional Search without volume Keyword: {search_three}"
                        )
                        no_volume_keyword_results = search_google_books(
                            0,
                            volume.path,
                            search_three,
                            max_results_num=30 if len(dir_files) <= 30 else 40,
                            in_line_search=False,
                        )
                        if no_volume_keyword_results:
                            clean_no_volume_keyword_results = clean_api_results(
                                no_volume_keyword_results,
                                volume.volume_number,
                                first_word_in_series,
                                volume.multi_volume,
                                volume.series_name,
                                volume.extension,
                                volume.volume_part,
                                skip_series_similarity=True,
                                skip_vol_nums_equal=True,
                                skip_omnibus_check=True,
                            )
                            cleaned_results.extend(
                                [
                                    result
                                    for result in clean_no_volume_keyword_results
                                    if result not in cleaned_results
                                ]
                            )

                    print(f"\nAdditional Search without volume Keyword: {search_three}")
                    no_volume_keyword_results_newest = search_google_books(
                        0,
                        volume.path,
                        search_three,
                        max_results_num=10,
                        in_line_search=False,
                        order_by="newest",
                    )
                    if no_volume_keyword_results_newest:
                        clean_no_volume_keyword_results_newest = clean_api_results(
                            no_volume_keyword_results_newest,
                            volume.volume_number,
                            first_word_in_series,
                            volume.multi_volume,
                            volume.series_name,
                            volume.extension,
                            volume.volume_part,
                            skip_series_similarity=True,
                            skip_vol_nums_equal=True,
                            skip_omnibus_check=True,
                        )
                        cleaned_results.extend(
                            [
                                result
                                for result in clean_no_volume_keyword_results_newest
                                if result not in cleaned_results
                            ]
                        )

                # search three without volume keyword + no category check
                if not series_info:
                    print(
                        f"\nAdditional Search without volume Keyword: {search_three}, with no category check."
                    )
                    no_volume_keyword_results_no_cat = search_google_books(
                        0,
                        volume.path,
                        search_three,
                        max_results_num=3,
                        in_line_search=True,
                    )
                    if no_volume_keyword_results_no_cat:
                        clean_no_volume_keyword_results_no_cat = clean_api_results(
                            no_volume_keyword_results,
                            volume.volume_number,
                            first_word_in_series,
                            volume.multi_volume,
                            volume.series_name,
                            volume.extension,
                            volume.volume_part,
                            skip_series_similarity=True,
                            skip_vol_nums_equal=True,
                            skip_categories_check=True,
                        )
                        if clean_no_volume_keyword_results_no_cat:
                            cleaned_results.extend(
                                [
                                    result
                                    for result in clean_no_volume_keyword_results_no_cat
                                    if result not in cleaned_results
                                ]
                            )

            if provider.name == "kobo":
                print(f"\nSearching Kobo with: {search}")
                kobo_results = []
                # search_with_and_instead_of_amp = re.sub(r"&", "and", search)
                kobo_search_results = text_search_kobo(search)
                # move any items that contain the voluem number to the front of the list
                if kobo_search_results and volume.volume_number:
                    kobo_search_results = sorted(
                        kobo_search_results,
                        key=lambda x: bool(
                            re.search(rf"\b0?{volume.volume_number}$", x)
                        ),
                        reverse=True,
                    )

                # kobo_search_with_and = text_search_kobo(search_with_and_instead_of_amp)
                # limit total web scraping to 5 results
                kobo_search_results = kobo_search_results[:5]
                # kobo_search_with_and = kobo_search_with_and[:10]
                # extend kobo_search_results with kobo_search_with_and
                # kobo_search_results.extend(kobo_search_with_and)
                # remove all results after 5
                if kobo_search_results:
                    for kobo_r in kobo_search_results:
                        data_result = get_kobo_books_meta(
                            kobo_r, 0, "", None, text_search=True
                        )
                        if data_result and data_result not in kobo_results:
                            kobo_results.append(data_result)
                        kobo_sleep_time = 10 + random.randint(3, 9)
                        print(f"\n\t\tSleeping for {kobo_sleep_time} seconds...\n")
                        time.sleep(kobo_sleep_time)
                else:
                    print("\tNo results found.")

                if kobo_results:
                    clean_kobo_results = clean_api_results(
                        kobo_results,
                        volume.volume_number,
                        first_word_in_series,
                        volume.multi_volume,
                        volume.series_name,
                        volume.extension,
                        volume.volume_part,
                        skip_series_similarity=True,
                        skip_vol_nums_equal=True,
                        skip_omnibus_check=True,
                        skip_categories_check=True,
                    )
                    cleaned_results.extend(
                        [
                            result
                            for result in clean_kobo_results
                            if result not in cleaned_results
                        ]
                    )

            if provider.name == "bookwalker":
                bw_category = "l" if volume.extension == ".epub" else "m"

                bookwalker_results = []
                print(f"\nSearching Bookwalker with: {search_five}")

                bookwalker_search_results = text_search_bookwalker(
                    search_five, bw_category
                )
                if bookwalker_search_results:
                    for bookwalker_r in bookwalker_search_results:
                        data_result = get_bookwalker_books_meta(bookwalker_r)
                        if data_result and data_result not in bookwalker_results:
                            bookwalker_results.append(data_result)
                        print(
                            f"\n\t\tSleeping for {web_scrape_sleep_time} seconds...\n"
                        )
                        time.sleep(web_scrape_sleep_time)
                else:
                    print("\tNo results found.")
                bw_limit = 20
                print(
                    f"\nSearching Bookwalker with: {search_three}\n\tLimit: {bw_limit}"
                )
                no_volume_number_series_search_results = text_search_bookwalker(
                    search_three, bw_category, bw_limit
                )
                if no_volume_number_series_search_results:
                    for bookwalker_r in no_volume_number_series_search_results:
                        data_result = get_bookwalker_books_meta(bookwalker_r)
                        if data_result and data_result not in bookwalker_results:
                            bookwalker_results.append(data_result)
                        print(
                            f"\n\t\tSleeping for {web_scrape_sleep_time} seconds...\n"
                        )
                        time.sleep(web_scrape_sleep_time)
                if bookwalker_results:
                    clean_bookwalker_results = clean_api_results(
                        bookwalker_results,
                        volume.volume_number,
                        first_word_in_series,
                        volume.multi_volume,
                        volume.series_name,
                        volume.extension,
                        volume.volume_part,
                        skip_series_similarity=True,
                        skip_vol_nums_equal=True,
                        skip_omnibus_check=True,
                        skip_categories_check=True,
                    )
                    cleaned_results.extend(
                        [
                            result
                            for result in clean_bookwalker_results
                            if result not in cleaned_results
                        ]
                    )

            if provider.name == "barnes_and_noble":
                barnes_results = []
                print(f"\nSearching Barnes and Noble with: {search_five}")

                bn_search_results = text_search_barnes_and_noble(search_five)
                if bn_search_results and isinstance(bn_search_results, list):
                    for bn_r in bn_search_results:
                        data_result = get_barnes_and_noble_books_meta(bn_r)
                        if data_result and data_result not in barnes_results:
                            barnes_results.append(data_result)
                        print(
                            f"\n\t\tSleeping for {web_scrape_sleep_time} seconds...\n"
                        )
                        time.sleep(web_scrape_sleep_time)
                elif bn_search_results and hasattr(bn_search_results, "isbn"):
                    barnes_results = [bn_search_results]
                else:
                    print("\tNo search results found")
                if barnes_results:
                    clean_barnes_results = clean_api_results(
                        barnes_results,
                        volume.volume_number,
                        first_word_in_series,
                        volume.multi_volume,
                        volume.series_name,
                        volume.extension,
                        volume.volume_part,
                        skip_series_similarity=True,
                        skip_vol_nums_equal=True,
                        skip_omnibus_check=True,
                        skip_categories_check=True,
                    )
                    cleaned_results.extend(
                        [
                            result
                            for result in clean_barnes_results
                            if result not in cleaned_results
                        ]
                    )

            if (
                provider.name == "comic_vine"
                and comic_vine_api_key
                and volume.extension == ".cbz"
            ):
                comic_vine_results = []
                print(f"\nSearching Comic Vine with: {search_five}")

                comic_vine_results = search_comic_vine(search_five, comic_vine_api_key)
                print(f"\n\tSleeping for {comic_vine_sleep_time} seconds...\n")
                time.sleep(comic_vine_sleep_time)
                if comic_vine_results:
                    clean_comic_vine_results = clean_api_results(
                        comic_vine_results,
                        volume.volume_number,
                        first_word_in_series,
                        volume.multi_volume,
                        volume.series_name,
                        volume.extension,
                        volume.volume_part,
                        skip_series_similarity=False,
                        skip_vol_nums_equal=True,
                        skip_omnibus_check=True,
                        skip_categories_check=True,
                        series_similarity_score=0.8,
                    )
                    if clean_comic_vine_results:
                        cleaned_results.extend(
                            [
                                result
                                for result in clean_comic_vine_results
                                if result not in cleaned_results
                            ]
                        )

            if (
                provider.name == "cached_series_id_results"
                and cached_series_result
                and successful_match
            ):
                print("\tUsing cached result...")
                session_result = cached_series_result
                series_info = session_result.results
                cleaned_results = cached_series_result.api_results

                for result in session_result.api_results:
                    if result not in cleaned_results:
                        cleaned_results.append(result)

                    if (
                        not len(session_result.series_id) > 1
                        and (
                            result.series_id_order_number != ""
                            and volume.volume_number != ""
                        )
                        and (result.series_id_order_number == volume.volume_number)
                        and result.series_id_order_number == result.volume
                        and result not in series_id_w_matching_vol_to_ord_num
                    ):
                        series_id_w_matching_vol_to_ord_num.append(result)

            # remove any duplicate results from cleaned_results by matching api_link
            cleaned_results = list(dict.fromkeys(cleaned_results))

            results_with_image_score = []

            # if (
            #     len(series_id_w_matching_vol_to_ord_num) == 1
            #     and "bookworm" not in volume.series_name.lower()
            # ):
            #     results_with_image_score.append(Image_Result(None, 0, None))

            if not results_with_image_score:
                if cleaned_results:
                    print(f"\nTotal results: {len(cleaned_results)}")
                    for result in cleaned_results:
                        try:
                            print(
                                f"\tResult {cleaned_results.index(result) + 1} of {len(cleaned_results)}:"
                            )
                            print(f"\t\tSeries: {result.series}")
                            print(f"\t\tVolume: {result.volume}")
                            print(f"\t\tISBN: {result.isbn}")
                            print(f"\t\tAPI Link: {result.api_link}")
                            print(f"\t\tLink: {result.preview_link}")

                            if result.image_links:
                                print(
                                    f"\t\tTotal Image Links: {len(result.image_links)}"
                                )
                                if (
                                    not multi_process_image_links
                                    and not successful_match
                                ):
                                    for link in result.image_links:
                                        image_result = process_image_link(
                                            result,
                                            cover,
                                            link,
                                            internal_cover_data,
                                            session_result,
                                            provider.name,
                                        )
                                        if image_result:
                                            results_with_image_score.append(
                                                image_result
                                            )
                                else:
                                    with concurrent.futures.ThreadPoolExecutor() as executor:
                                        worker = partial(
                                            process_image_link,
                                            result,
                                            cover,
                                            internal_cover_data=internal_cover_data,
                                            session_result_data=session_result,
                                            provider_name=provider.name,
                                        )
                                        results = executor.map(
                                            worker, result.image_links
                                        )
                                        if results:
                                            for result in results:
                                                if result:
                                                    results_with_image_score.append(
                                                        result
                                                    )
                        except Exception as e:
                            send_message(str(e), error=True)
                            write_to_file("isbn_script_errors.txt", str(e))
                            continue
                else:
                    send_message("\tNo results left after heavy filtering.")

            if results_with_image_score:
                results_with_image_score.sort(
                    key=lambda x: x.ssim_score,
                    reverse=True,
                )
                best_result = results_with_image_score[0]
                passed = False

                if best_result.ssim_score >= required_image_ssim_score:
                    passed = True
                elif len(series_id_w_matching_vol_to_ord_num) == 1:
                    passed = True
                    best_result = Image_Result(
                        series_id_w_matching_vol_to_ord_num[0],
                        0,
                        series_id_w_matching_vol_to_ord_num[0].image_links[0],
                    )
                else:
                    series_id_w_matching_vol_to_ord_num = []

                if passed:
                    # Combine all arrays into a list of tuples, with each tuple containing the element and the array name
                    # all_arrays = [
                    #     ("clean_r_results", clean_r_results),
                    #     ("clean_b_results", clean_b_results),
                    #     (
                    #         "clean_no_volume_keyword_results",
                    #         clean_no_volume_keyword_results,
                    #     ),
                    #     (
                    #         "clean_no_volume_keyword_results_newest",
                    #         clean_no_volume_keyword_results_newest,
                    #     ),
                    #     (
                    #         "clean_no_volume_keyword_results_no_cat",
                    #         clean_no_volume_keyword_results_no_cat,
                    #     ),
                    # ]

                    # # Dictionary to store frequency of each element in different arrays
                    # frequency_dict = defaultdict(lambda: defaultdict(int))

                    # for array_name, array in all_arrays:
                    #     for element in array:
                    #         frequency_dict[element][array_name] += 1

                    # # Identify elements that appear in two or more arrays
                    # duplicates_in_multiple_arrays = {
                    #     element: arrays
                    #     for element, arrays in frequency_dict.items()
                    #     if len(arrays) > 1
                    # }

                    # # Identify elements that are unique (found in only one array)
                    # unique_elements = {}
                    # array_names = []
                    # for element, arrays in frequency_dict.items():
                    #     if len(arrays) == 1 and arrays not in array_names:
                    #         unique_elements[element] = arrays
                    #         array_names.append(arrays)

                    # # Log the duplicate
                    # for element, arrays in duplicates_in_multiple_arrays.items():
                    #     message = f"{element.api_link}:"
                    #     last_element = list(arrays.keys())[-1]
                    #     for array_name, count in arrays.items():
                    #         message += (
                    #             f"{array_name}" + ","
                    #             if array_name != last_element
                    #             else f"{array_name}"
                    #         )
                    #     write_to_file(
                    #         "duplicates_report.txt",
                    #         message,
                    #         without_timestamp=True,
                    #         check_for_dup=True,
                    #     )

                    # # Log the unique elements
                    # if not duplicates_in_multiple_arrays:
                    #     for element, arrays in unique_elements.items():
                    #         array_name = next(
                    #             iter(arrays)
                    #         )  # Get the only array name where this element is found
                    #         message = f"{element.api_link}:{array_name}"
                    #         write_to_file(
                    #             "unique_elements_report.txt",
                    #             message,
                    #             without_timestamp=True,
                    #             check_for_dup=True,
                    #         )

                    if (
                        session_result
                        and hasattr(session_result, "api_results")
                        and session_result.api_results
                        and not successful_match
                    ):
                        for session_api_result in session_result.api_results:
                            if session_api_result.api_link == best_result.book.api_link:
                                cached_series_result = session_result
                                successful_match = True
                                break
                    if series_id_w_matching_vol_to_ord_num and not (
                        best_result.ssim_score >= required_image_ssim_score
                    ):
                        send_message(
                            "\nmatch found through series_id_order_number match with one result."
                        )
                    best_result.book.series = volume.series_name
                    best_result.book.number = volume.volume_number
                    best_result.book.volume = volume.volume_number
                    best_result.book.part = volume.volume_part

                    if (
                        not session_result
                        and best_result.book.series_id
                        and not best_result.book.title.startswith("Volume")
                    ):
                        # scrape series_id results subtitles
                        # and replace the title if a duplicate subtitle is found
                        series_ids = scrape_series_ids(
                            best_result.book.series_id.split("series_id:")[1]
                        )

                        if series_ids:
                            for item in series_ids:
                                # scrape from google books
                                series_search = search_google_books(
                                    0,
                                    volume.path,
                                    volume_id=item,
                                    max_results_num=40,
                                    mute_output=True,
                                )
                                time.sleep(sleep_time)
                                ps_obj = PossibleSubtitle(
                                    "title", series_search.subtitle
                                )

                                if series_search and series_search.subtitle:
                                    if ps_obj not in file_descriptions:
                                        file_descriptions.append(ps_obj)
                                    if ps_obj not in result_subtitles:
                                        result_subtitles.append(ps_obj)

                            if check_description_match(
                                file_descriptions,
                                best_result.book.title,
                                volume.series_name,
                            ):
                                volume_keyword = ""
                                if isinstance(best_result.book.number, list):
                                    volume_keyword = "Volumes "
                                    best_result.book.title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume.volume_number)}"
                                else:
                                    volume_keyword = "Volume "
                                    best_result.book.title = (
                                        f"{volume_keyword}{volume.volume_number}"
                                    )

                    if re.search(
                        r"Volumes?",
                        best_result.book.title,
                        re.IGNORECASE,
                    ):
                        volume_keyword = ""
                        if isinstance(best_result.book.number, list):
                            volume_keyword = "Volumes "
                            best_result.book.title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume.volume_number)}"
                        else:
                            volume_keyword = "Volume "
                            best_result.book.title = (
                                f"{volume_keyword}{volume.volume_number}"
                            )

                        if volume.volume_part:
                            best_result.book.title = (
                                f"{best_result.book.title} Part {volume.volume_part}"
                            )
                    if (
                        not best_result.book.title
                        and volume.volume_number != ""
                        and volume.volume_part
                    ):
                        volume_keyword = ""
                        if isinstance(best_result.book.number, list):
                            volume_keyword = "Volumes "
                            best_result.book.title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume.volume_number)} Part {volume.volume_part}"
                        else:
                            volume_keyword = "Volume "
                            best_result.book.title = f"{volume_keyword}{volume.volume_number} Part {volume.volume_part}"
                    elif (
                        not best_result.book.title
                        and volume.volume_number != ""
                        and not volume.volume_part
                    ):
                        volume_keyword = ""
                        if isinstance(best_result.book.number, list):
                            volume_keyword = "Volumes "
                            best_result.book.title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume.volume_number)}"
                        else:
                            volume_keyword = "Volume "
                            best_result.book.title = (
                                f"{volume_keyword}{volume.volume_number}"
                            )

                    write_to_file(
                        "items_found_through_image_comparision_search.txt",
                        volume.path,
                    )
                    return best_result
                else:
                    cached_series_result = None
                    successful_match = False
                    image_link_cache = []

                    send_message(
                        f"\tHighest SSIM Score: {best_result.ssim_score} is less than the required score of {required_image_ssim_score}"
                    )
                    if best_result.image_link:
                        print(f"\tImage Link: {best_result.image_link}")
                    if best_result.book.api_link:
                        print(f"\tAPI Link: {best_result.book.api_link}")
                    if best_result.book.series:
                        print(f"\tSeries: {best_result.book.series}")
                    # if best_result.book.volume:
                    #     print(f"\tVolume: {best_result.book.volume}")
                    if best_result.book.isbn:
                        print(f"\tISBN: {best_result.book.isbn}")
                    if best_result.book.preview_link:
                        print(f"\tLink: {best_result.book.preview_link}")

                    write_to_file(
                        "items_not_found_through_image_comparision_search.txt",
                        volume.path,
                        without_timestamp=True,
                    )
                    items_not_found_through_image_comparision_search.append(volume.path)
                    if volume.extension == ".epub" and not volume.multi_volume:
                        num = volume.volume_number
                        if isinstance(num, list):
                            num = num[0]
                        data = get_epub_metadata(volume.path)
                        if volume.volume_part:
                            num = float(f"{num}.{volume.volume_part}")
                        if num != data.number:
                            update_metadata(
                                "ebook-meta",
                                volume.path,
                                None,
                                num,
                                "Index Number",
                                "-i",
                                skip_print=manualmetadata == False,
                            )
                        if volume.series_name != data.series:
                            update_metadata(
                                "ebook-meta",
                                volume.path,
                                data.series,
                                volume.series_name,
                                "Series",
                                "--series",
                                skip_print=manualmetadata == False,
                            )
            else:
                # send_message("\tNo image score results.")
                write_to_file(
                    "items_not_found_through_image_comparision_search.txt",
                    volume.path,
                    without_timestamp=True,
                )
                items_not_found_through_image_comparision_search.append(volume.path)
                if volume.extension == ".epub" and not volume.multi_volume:
                    num = volume.volume_number
                    if isinstance(num, list):
                        num = num[0]
                    data = get_epub_metadata(volume.path)
                    if volume.volume_part:
                        num = float(f"{num}.{volume.volume_part}")
                    if num != data.number:
                        update_metadata(
                            "ebook-meta",
                            volume.path,
                            None,
                            num,
                            "Index Number",
                            "-i",
                            skip_print=manualmetadata == False,
                        )
                    if volume.series_name != data.series:
                        update_metadata(
                            "ebook-meta",
                            volume.path,
                            data.series,
                            volume.series_name,
                            "Series",
                            "--series",
                            skip_print=manualmetadata == False,
                        )

    else:
        if not cover:
            send_message(f"\tNo cover image found for {volume.path}", error=True)

        if skip_image_comparison:
            send_message("skip_image_comparison=True, skipping...")

        write_to_file(
            "items_not_found_through_image_comparision_search.txt",
            volume.path,
            without_timestamp=True,
        )
        items_not_found_through_image_comparision_search.append(volume.path)

        if volume.extension == ".epub" and not volume.multi_volume:
            num = volume.volume_number
            if isinstance(num, list):
                num = num[0]

            # Get metadata from the EPUB file
            data = get_epub_metadata(volume.path)

            if volume.volume_part:
                num = float(f"{num}.{volume.volume_part}")

            # Update the index number if it's different from the metadata
            if num != data.number:
                update_metadata(
                    "ebook-meta",
                    volume.path,
                    None,
                    num,
                    "Index Number",
                    "-i",
                    skip_print=manualmetadata == False,
                )

            # Update the series name if it's different from the metadata
            if volume.series_name != data.series:
                update_metadata(
                    "ebook-meta",
                    volume.path,
                    data.series,
                    volume.series_name,
                    "Series",
                    "--series",
                    skip_print=manualmetadata == False,
                )
    return None


# open ComicInfo.xml from the passed zip file, and return the xml contents as a string
def get_comic_info_xml(zip_file):
    with zipfile.ZipFile(zip_file, "r") as z:
        list = z.namelist()
        for file in list:
            if file == "ComicInfo.xml" and "__MACOSX" not in file.upper():
                return z.read(file).decode("utf-8")
    return None


# check if zip file contains ComicInfo.xml
def contains_comic_info(zip_file):
    result = False
    try:
        with zipfile.ZipFile(zip_file, "r") as zip_ref:
            if "comicinfo.xml" in map(str.lower, zip_ref.namelist()):
                result = True
    except (zipfile.BadZipFile, FileNotFoundError) as e:
        send_message(f"\tFile: {zip_file}\n\t\tERROR: {e}", error=True)
    return result


# get age of file and return in minutes based on modification time
def get_modiciation_age(file):
    return int(time.time() - os.path.getmtime(file)) / 60


# get age of file and return in minutes based on creation time
def get_creation_age(file):
    return int(time.time() - os.path.getctime(file)) / 60


# regex out underscore from passed string and return it
@lru_cache(maxsize=None)
def replace_underscores(name):
    # Replace underscores that are preceded and followed by a number with a period
    name = re.sub(r"(?<=\d)_(?=\d)", ".", name)

    # Replace all other underscores with a space
    name = name.replace("_", " ")
    name = remove_dual_space(name).strip()

    return name


def process_file(volume, files, file_only=False):
    zip_comments = str(get_zip_comment(volume.path))

    if skip_if_has_zip_comment and zip_comments:
        print("\tSkipping file because it already has a zip comment.")
        print(f"\t\tZip Comment: {zip_comments}")
        return None

    if skip_volumes_older_than_x_time and os.path.isfile(volume.path):
        if (
            get_modiciation_age(volume.path) >= skip_volumes_older_than_x_time
            and get_creation_age(volume.path) >= skip_volumes_older_than_x_time
        ):
            print(
                f"\tSkipping {volume.name} because it is older than {skip_volumes_older_than_x_time} minutes"
            )
            return None

    try:
        if isinstance(volume.volume_number, list):
            if skip_non_volume_ones and 1 not in volume.volume_number:
                print("\tSkip non-volume one files enabled, skipping...")
                return None
            elif skip_volume_one and 1 in volume.volume_number:
                print("\tSkip volume one files enabled, skipping...")
                return None
        else:
            if (skip_non_volume_ones and volume.volume_number != 1) or (
                skip_volume_one and volume.volume_number == 1
            ):
                print("\tSkip non-volume one files enabled, skipping...")
                return None

        if skip_volume_if_already_has_anilist_id:
            if "anilist_id" in zip_comments:
                print(f"\tSkipping {volume.name} because it already has an anilist_id")
                return None
            elif volume.extension == ".epub" and get_meta_from_file(
                volume.path, r"(\<dc\:subject\>)", volume.extension
            ):
                print(f"\tSkipping {volume.name} because it already has an anilist_id")
                return None
        if skip_volume_if_already_has_volume_id:
            if "volume_id" in zip_comments:
                print(f"\tSkipping {volume.name} because it already has a volume_id")
                return None
        if skip_volume_if_already_has_series_id:
            if "series_id" in zip_comments:
                print(f"\tSkipping {volume.name} because it already has a series_id")
                return None

        result = ""
        cleaned_result = ""

        if volume.extension == ".cbz":
            has_comic_info = contains_comic_info(volume.path)
            if has_comic_info:
                comic_info_contents = get_comic_info_xml(volume.path)

                if skip_web_link and comic_info_contents:
                    contents = parse_comicinfo_xml(comic_info_contents)
                    if contents and "Web" in contents:
                        print("\tcontains web links, skipping...")
                        return None

                if skip_all_non_comic_tagger_tagged and not skip_comic_info:
                    if comic_info_contents:
                        if not re.search(
                            r"ComicTagger", comic_info_contents, re.IGNORECASE
                        ):
                            print("\tnot tagged by comictagger, skipping...")
                            return None
                    else:
                        send_message(
                            f"\t{volume.name} has comic_info, but no contents.",
                            error=True,
                        )
                        write_to_file(
                            "found_comic_info_but_no_contents.txt",
                            volume.path,
                            without_timestamp=True,
                            check_for_dup=True,
                        )

                if skip_google_metadata and comic_info_contents:
                    if re.search(r"googleapis", comic_info_contents, re.IGNORECASE):
                        print("\tcontains google metadata, skipping...")
                        return None
                    else:
                        comic_info_contents_xml = parse_comicinfo_xml(
                            comic_info_contents
                        )
                        if comic_info_contents_xml and "Web" in comic_info_contents_xml:
                            # print web tag
                            if comic_info_contents_xml["Web"]:
                                print(f"\tWeb: {comic_info_contents_xml['Web']}")

            elif (
                not has_comic_info
                and skip_all_non_comic_tagger_tagged
                and not skip_comic_info
            ):
                print("\tno comicinfo contents found, skipping")
                return None

            if skip_file_if_isbn_in_zip_comment and zip_comments:
                if re.search(rf"{isbn_13_regex}", zip_comments):
                    print(f"\n{volume.name} already contains isbn, skipping...")
                    print(f"\t{zip_comments}")
                    return None

            elif skip_comic_info and has_comic_info:
                contents = parse_comicinfo_xml(comic_info_contents)

                if (
                    contents
                    and "Title" in contents
                    and "Summary" in contents
                    and not any(
                        re.search(exclusion, contents["Title"], re.IGNORECASE)
                        for exclusion in subtitle_exclusion_keywords
                    )
                    and not contents["Title"][0].islower()
                ):
                    print(
                        f"\t{volume.name} already contains ComicInfo.xml, skipping..."
                    )
                    return None

        elif volume.extension == ".epub":
            if skip_novels_with_metadata:
                epub_metadata = get_epub_metadata(volume.path)
                if epub_metadata:
                    series_no_meta = remove_punctuation(volume.series_name)
                    series_no_meta_half = series_no_meta[: int(len(series_no_meta) / 2)]
                    title_no_meta = remove_punctuation(epub_metadata.title)
                    if (
                        epub_metadata.comments
                        and not re.search(
                            series_no_meta,
                            title_no_meta,
                            re.IGNORECASE,
                        )
                        and not re.search(
                            series_no_meta_half,
                            title_no_meta,
                            re.IGNORECASE,
                        )
                        and not any(
                            re.search(exclusion, title_no_meta, re.IGNORECASE)
                            for exclusion in subtitle_exclusion_keywords
                        )
                    ):
                        print("\t already contains metadata, skipping...")
                        return None

        send_discord_message(
            None,
            "File",
            color=8421504,
            fields=[
                {
                    "name": "Name",
                    "value": volume.name,
                    "inline": False,
                },
                {
                    "name": "Location",
                    "value": volume.root,
                    "inline": False,
                },
            ],
        )

        global cached_series_result
        global successful_match
        global image_link_cache
        global file_descriptions

        if volume.extension in file_extensions:
            if file_only:
                file_paths = [file.path for file in files]

                additional_files = clean_and_sort(
                    volume.root,
                    [file for file in os.listdir(volume.root) if os.path.isfile(file)],
                )[0]

                # upgrade to volumes
                additional_volumes = upgrade_to_volume_class(
                    upgrade_to_file_class(
                        [
                            f
                            for f in additional_files
                            if os.path.isfile(os.path.join(volume.root, f))
                        ],
                        volume.root,
                    )
                )

                # extend files not currently in the files list
                files.extend(
                    [file for file in additional_volumes if file.path not in file_paths]
                )

            # Remove any files that have the same volume number
            # as the current volume that we're processing
            dir_files = [
                file
                for file in files
                if file.path != volume.path and file.extension in file_extensions
            ]

            file_descriptions = [PossibleSubtitle("title", volume.series_name)]
            file_descriptions.extend(result_subtitles)

            # set the variable to the file extension if all of the files have the same extension
            use_multi = volume.extension == ".epub" and all(
                file.extension == volume.extension for file in dir_files
            )
            # use_multi = True

            if use_multi:
                with concurrent.futures.ThreadPoolExecutor() as executor:
                    results = executor.map(
                        get_file_metadata,
                        [x.path for x in dir_files],
                    )
                    for result in results:
                        if not result:
                            continue

                        if result.comments:
                            file_descriptions.append(
                                PossibleSubtitle("comment", result.comments)
                            )
                        if result.title and not result.title.lower().startswith(
                            "volume"
                        ):
                            file_descriptions.append(
                                PossibleSubtitle("title", result.title)
                            )
            else:
                for file in dir_files:
                    result = get_file_metadata(file.path)
                    if not result:
                        continue

                    if result.comments:
                        file_descriptions.append(
                            PossibleSubtitle("comment", result.comments)
                        )
                    if result.title and not result.title.lower().startswith("volume"):
                        file_descriptions.append(
                            PossibleSubtitle("title", result.title)
                        )

        previous_provider = None

        for provider in providers:
            if (
                successful_match
                and cached_series_result
                and hasattr(cached_series_result, "series_name")
            ):
                if (
                    similar(
                        remove_punctuation(cached_series_result.series_name),
                        remove_punctuation(volume.series_name),
                    )
                    >= required_similarity_score
                ):
                    previous_provider = cached_provider
                    result = search_provider(
                        volume,
                        cached_provider,
                        zip_comments,
                        dir_files=files,
                    )
                    if result:
                        break
                else:
                    successful_match = False
                    cached_series_result = None
                    image_link_cache = []

            if provider.enabled:
                previous_provider = provider
                result = search_provider(
                    volume,
                    provider,
                    zip_comments,
                    dir_files=files,
                )
                if result:
                    break
                elif previous_provider.name == "google-books":
                    if not result and (
                        not only_image_comparision or volume.extension == ".cbz"
                    ):
                        print(
                            f"{'-'*64}\nBACKUP: Searching Internal Contents for an ISBN...\n{'-'*64}"
                        )
                        result = process_zip_file_contents(volume.path)

                        if result:
                            clean_results = [result.book]
                            volume_id_result = search_google_books(
                                0,
                                volume.path,
                                volume_id=result.book.google_volume_id,
                                max_results_num=40,
                            )
                            if volume_id_result:
                                clean_results.append(volume_id_result)
                            clean_results = clean_api_results(
                                clean_results,
                                volume.volume_number,
                                "",
                                volume.multi_volume,
                                volume.series_name,
                                volume.extension,
                                volume.volume_part,
                                skip_contains_first_word=True,
                                skip_omnibus_check=True,
                                skip_isebook_check=True,
                            )
                            if clean_results:
                                result = Result(clean_results[-1], None)
                                result.book.series = volume.series_name
                                result.book.number = volume.volume_number
                                result.book.volume = volume.volume_number
                                result.book.part = volume.volume_part
                                if re.search(
                                    r"Volumes?",
                                    result.book.title,
                                    re.IGNORECASE,
                                ):
                                    volume_keyword = ""
                                    if isinstance(result.book.number, list):
                                        volume_keyword = "Volumes "
                                        result.book.title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume.volume_number)}"
                                    else:
                                        volume_keyword = "Volume "
                                        result.book.title = (
                                            f"{volume_keyword}{volume.volume_number}"
                                        )
                                    if volume.volume_part:
                                        result.book.title = f"{result.book.title} Part {volume.volume_part}"
                                if (
                                    not result.book.title
                                    and volume.volume_number != ""
                                    and volume.volume_part
                                ):
                                    volume_keyword = ""
                                    if isinstance(result.book.number, list):
                                        volume_keyword = "Volumes "
                                        result.book.title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume.volume_number)} Part {volume.volume_part}"
                                    else:
                                        volume_keyword = "Volume "
                                        result.book.title = f"{volume_keyword}{volume.volume_number} Part {volume.volume_part}"
                                elif (
                                    not result.book.title
                                    and volume.volume_number != ""
                                    and not volume.volume_part
                                ):
                                    volume_keyword = ""
                                    if isinstance(result.book.number, list):
                                        volume_keyword = "Volumes "
                                        result.book.title = f"{volume_keyword}{convert_array_to_string_with_dashes(volume.volume_number)}"
                                    else:
                                        volume_keyword = "Volume "
                                        result.book.title = (
                                            f"{volume_keyword}{volume.volume_number}"
                                        )
                            else:
                                result = None
                    if (
                        result
                        and hasattr(result, "book")
                        and result.book.number == volume.volume_number
                        and result.book.summary
                        and ((result.book.is_ebook) or allow_non_is_ebook_results)
                        or (
                            result
                            and hasattr(result, "book")
                            and square_enix_bypass
                            and re.search(
                                r"Square", result.book.publisher, re.IGNORECASE
                            )
                            and re.search(r"Enix", result.book.publisher, re.IGNORECASE)
                        )
                    ):
                        break
            else:
                print(f"\n\t{provider.name} is disabled, skipping...")

        # if result and hasattr(result, "book"):
        #     if result.book.number == volume.volume_number:
        #         if result.book.summary:
        #             print_book_result(result)
        #             write_metadata = compare_metadata(result.book, volume.path, files)
        #             items_found_through_ocr_on_epub.append(volume.path)
        #             write_to_file(
        #                 "items_found_through_ocr_on_epub.txt",
        #                 volume.path,
        #             )
        #             return result
        #         else:
        #             send_message(
        #                 f"\tFile: {volume.name}\n\t\tERROR: empty summary, skipping...",
        #                 error=True,
        #             )
        #     else:
        #         send_message(
        #             f"\tFile: {volume.name}\n\t\tvolume_number mismatch\n\t\tskipping...\n\t\tresult.book.number: {result.book.number}"
        #         )
        #         write_to_file(
        #             "volume_number_mismatch.txt",
        #             volume.path,
        #             without_timestamp=True,
        #             check_for_dup=True,
        #         )
        if result and hasattr(result, "book"):
            if result.book.number == volume.volume_number:
                if ((result.book.is_ebook) or allow_non_is_ebook_results) or (
                    square_enix_bypass
                    and re.search(r"Square", result.book.publisher, re.IGNORECASE)
                    and re.search(r"Enix", result.book.publisher, re.IGNORECASE)
                ):
                    if result.book.summary:
                        print_book_result(result)
                        write_metadata = compare_metadata(
                            result.book, volume.path, files
                        )
                        items_found_through_ocr_on_epub.append(volume.path)
                        write_to_file(
                            "items_found_through_ocr_on_epub.txt",
                            volume.path,
                        )
                        return result
                    else:
                        send_message(
                            f"\tFile: {volume.name}\n\t\tERROR: empty summary, skipping...",
                            error=True,
                        )
                else:
                    send_message(
                        f"\tFile: {volume.name}\n\t\tis_ebook=False\n\t\tskipping..."
                    )
            else:
                send_message(
                    f"\tFile: {volume.name}\n\t\tvolume_number mismatch\n\t\tskipping...\n\t\tresult.book.number: {result.book.number}"
                )
                write_to_file(
                    "volume_number_mismatch.txt",
                    volume.path,
                    without_timestamp=True,
                    check_for_dup=True,
                )
    except Exception as e:
        traceback.print_tb(e.__traceback__)
        send_message(str(e), error=True)
        write_to_file("isbn_script_errors.txt", str(e))
    return None


# Checks if the file name contains multiple numbers
@lru_cache(maxsize=None)
def has_multiple_numbers(file_name):
    return len(re.findall(r"\d+\.0+[1-9]+|\d+\.[1-9]+|\d+", file_name)) > 1


# Function to parse boolean arguments from string values
def parse_bool_argument(arg_value):
    return str(arg_value).lower().strip() == "true"


if __name__ == "__main__":
    # The mode that the user passed in, either a path or a file
    user_mode = "path"

    parser = image_arg_parser()
    args = parser.parse_args()

    if args.mute_settings_output:
        mute_settings_output = parse_bool_argument(args.mute_settings_output)

    print(f"\nScript Version: {script_version_text}")

    if not mute_settings_output:
        print("\nRun Settings:")

    # Handle webhook argument
    if args.webhook is not None:
        for item in args.webhook:
            if item:
                for hook in item:
                    if hook:
                        if r"\1" in hook:
                            hook = hook.split(r"\1")
                        if isinstance(hook, str):
                            if hook and hook not in discord_webhook_url:
                                discord_webhook_url.append(hook)
                        elif isinstance(hook, list):
                            for url in hook:
                                if url and url not in discord_webhook_url:
                                    discord_webhook_url.append(url)
    if not mute_settings_output:
        print(f"\twebhooks: {discord_webhook_url}")

    # Parse accepted file types
    if args.accepted_file_types:
        accepted_file_types = (
            args.accepted_file_types.split(",")
            if "," in args.accepted_file_types
            else [args.accepted_file_types]
        )
    if not mute_settings_output:
        print(f"\taccepted_file_types: {accepted_file_types}")

    if args.skip_if_has_zip_comment:
        skip_if_has_zip_comment = parse_bool_argument(args.skip_if_has_zip_comment)
    if not mute_settings_output:
        print(f"\tskip_if_has_zip_comment: {skip_if_has_zip_comment}")

    if args.skip_file_if_isbn_in_zip_comment:
        skip_file_if_isbn_in_zip_comment = parse_bool_argument(
            args.skip_file_if_isbn_in_zip_comment
        )
    if not mute_settings_output:
        print(f"\tskip_file_if_isbn_in_zip_comment: {skip_file_if_isbn_in_zip_comment}")

    if args.skip_all_non_comic_tagger_tagged:
        skip_all_non_comic_tagger_tagged = parse_bool_argument(
            args.skip_all_non_comic_tagger_tagged
        )
    if not mute_settings_output:
        print(f"\tskip_all_non_comic_tagger_tagged: {skip_all_non_comic_tagger_tagged}")

    if args.only_image_comparision:
        only_image_comparision = parse_bool_argument(args.only_image_comparision)
    if not mute_settings_output:
        print(f"\tonly_image_comparision: {only_image_comparision}")

    if args.skip_letters:
        skip_letters = True if args.skip_letters else False
        accepted_letters = args.skip_letters
    if not mute_settings_output:
        print(f"\tskip_letters: {skip_letters}")

    # Parse more boolean arguments
    if args.skip_comic_info:
        skip_comic_info = parse_bool_argument(args.skip_comic_info)
    if not mute_settings_output:
        print(f"\tskip_comic_info: {skip_comic_info}")

    if args.manualmetadata:
        manualmetadata = parse_bool_argument(args.manualmetadata)
    if not mute_settings_output:
        print(f"\tmanualmetadata: {manualmetadata}")

    if args.skip_updating_metadata:
        skip_updating_metadata = parse_bool_argument(args.skip_updating_metadata)
    if not mute_settings_output:
        print(f"\tskip_updating_metadata: {skip_updating_metadata}")

    if args.skip_novels_with_metadata:
        skip_novels_with_metadata = parse_bool_argument(args.skip_novels_with_metadata)
    if not mute_settings_output:
        print(f"\tskip_novels_with_metadata: {skip_novels_with_metadata}")

    if args.skip_non_volume_ones:
        skip_non_volume_ones = parse_bool_argument(args.skip_non_volume_ones)
    if not mute_settings_output:
        print(f"\tskip_non_volume_ones: {skip_non_volume_ones}")

    # Parse and check if the value is a number
    if (
        args.skip_volumes_older_than_x_time
        and args.skip_volumes_older_than_x_time.isdigit()
    ):
        skip_volumes_older_than_x_time = int(args.skip_volumes_older_than_x_time)
    if not mute_settings_output:
        print(f"\tskip_volumes_older_than_x_time: {skip_volumes_older_than_x_time}")

    # Set provider enabled status based on arguments
    if args.scrape_google:
        scrape_google = parse_bool_argument(args.scrape_google)
    if not mute_settings_output:
        print(f"\tscrape_google: {scrape_google}")

    if args.scrape_bookwalker:
        scrape_bookwalker = parse_bool_argument(args.scrape_bookwalker)
    if not mute_settings_output:
        print(f"\tscrape_bookwalker: {scrape_bookwalker}")

    if args.scrape_kobo:
        scrape_kobo = parse_bool_argument(args.scrape_kobo)
    if not mute_settings_output:
        print(f"\tscrape_kobo: {scrape_kobo}")

    if args.scrape_barnes_and_noble:
        scrape_barnes_and_noble = parse_bool_argument(args.scrape_barnes_and_noble)
    if not mute_settings_output:
        print(f"\tscrape_barnes_and_noble: {scrape_barnes_and_noble}")

    if args.scrape_comic_vine:
        scrape_comic_vine = parse_bool_argument(args.scrape_comic_vine)
    if not mute_settings_output:
        print(f"\tscrape_comic_vine: {scrape_comic_vine}")

    # Set the provider enabled status based on arguments
    if (
        args.scrape_google
        or args.scrape_bookwalker
        or args.scrape_kobo
        or args.scrape_barnes_and_noble
        or args.scrape_comic_vine
    ):
        provider_enabled = [
            scrape_google,
            scrape_kobo,
            scrape_barnes_and_noble,
            scrape_bookwalker,
            scrape_comic_vine,
        ]
        for provider, enabled in zip(providers, provider_enabled):
            if provider.name in provider_names:
                provider.enabled = enabled

    # Parse more boolean arguments
    if args.skip_volume_if_already_has_anilist_id:
        skip_volume_if_already_has_anilist_id = parse_bool_argument(
            args.skip_volume_if_already_has_anilist_id
        )
    if not mute_settings_output:
        print(
            f"\tskip_volume_if_already_has_anilist_id: {skip_volume_if_already_has_anilist_id}"
        )

    if args.skip_volume_if_already_has_volume_id:
        skip_volume_if_already_has_volume_id = parse_bool_argument(
            args.skip_volume_if_already_has_volume_id
        )
    if not mute_settings_output:
        print(
            f"\tskip_volume_if_already_has_volume_id: {skip_volume_if_already_has_volume_id}"
        )

    if args.skip_volume_if_already_has_series_id:
        skip_volume_if_already_has_series_id = parse_bool_argument(
            args.skip_volume_if_already_has_series_id
        )

    if args.skip_google_metadata:
        skip_google_metadata = parse_bool_argument(args.skip_google_metadata)
    if not mute_settings_output:
        print(f"\tskip_google_metadata: {skip_google_metadata}")

    if args.use_internal_cover:
        use_internal_cover = parse_bool_argument(args.use_internal_cover)
    if not mute_settings_output:
        print(f"\tuse_internal_cover: {use_internal_cover}")

    if args.skip_volume_one:
        skip_volume_one = parse_bool_argument(args.skip_volume_one)
    if not mute_settings_output:
        print(f"\tskip_volume_one: {skip_volume_one}")

    if args.skip_web_link:
        skip_web_link = parse_bool_argument(args.skip_web_link)
    if not mute_settings_output:
        print(f"\tskip_web_link: {skip_web_link}")

    if args.only_update_if_new_title:
        only_update_if_new_title = parse_bool_argument(args.only_update_if_new_title)
    if not mute_settings_output:
        print(f"\tonly_update_if_new_title: {only_update_if_new_title}")

    # Parse skip_to_file and skip_to_directory arguments
    if args.skip_to_file:
        skip_to_file = str(args.skip_to_file).strip()
    if not mute_settings_output:
        print(f"\tskip_to_file: {skip_to_file}")

    if args.skip_to_directory:
        skip_to_directory = str(args.skip_to_directory).strip()
    if not mute_settings_output:
        print(f"\tskip_to_directory: {skip_to_directory}")

    # Parse more boolean arguments
    if args.skip_non_digital_manga:
        skip_non_digital_manga = parse_bool_argument(args.skip_non_digital_manga)
    if not mute_settings_output:
        print(f"\tskip_non_digital_manga: {skip_non_digital_manga}")

    if args.manual_series_id_mode:
        manual_series_id_mode = parse_bool_argument(args.manual_series_id_mode)

    if args.manual_zip_comment_approval:
        manual_zip_comment_approval = parse_bool_argument(
            args.manual_zip_comment_approval
        )
    if not mute_settings_output:
        print(f"\tmanual_zip_comment_approval: {manual_zip_comment_approval}")

    stop = False
    path = args.path
    file = args.file

    if path or file:
        # file = "/mnt/drive_three/manga/public/A Bride's Story/A Bride's Story v10 (2018) (Yen Press) (Digital) (danke-Empire).cbz"
        if file:
            user_mode = "file"
            path = os.path.dirname(file)

        if os.path.isdir(path):
            # path = "/mnt/drive_three/novels/public/The Fruit of Evolution - Before I Knew It, My Life Had It Made!"
            os.chdir(path)
            adjusted_dirs = []
            for root, dirs, files in scandir.walk(path, topdown=True):
                # reset result_subtitles
                result_subtitles = []

                if file:
                    files = [os.path.basename(file)]

                clean = clean_and_sort(
                    root,
                    files,
                    dirs,
                    sort=(
                        True
                        if (
                            (args.sort and args.sort.lower() == "true")
                            or (skip_to_directory or skip_to_file)
                        )
                        else False
                    ),
                )

                files, dirs = clean[0], clean[1]

                if skip_to_file:
                    if skip_to_file in files:
                        skip_to_file = None
                    else:
                        continue

                if root == path:
                    # Remove all that aren't specified in skip_letters
                    if skip_letters and accepted_letters:
                        if not re.search(
                            rf"^({accepted_letters})", root, re.IGNORECASE
                        ):
                            continue
                        else:
                            accepted_letters = None

                    # Skip all directories until we reach the one specified
                    if skip_to_directory:
                        if skip_to_directory in dirs:
                            adjusted_dirs = dirs[dirs.index(skip_to_directory) :]
                            skip_to_directory = None

                if adjusted_dirs:
                    if os.path.basename(root) not in adjusted_dirs:
                        continue
                    else:
                        adjusted_dirs = []

                if not files:
                    continue

                print(f"\nRoot: {root}")
                print(f"Files: {files}")

                volumes = upgrade_to_volume_class(
                    upgrade_to_file_class(
                        [f for f in files if os.path.isfile(os.path.join(root, f))],
                        root,
                    )
                )

                result = None

                if not volumes:
                    continue

                if stop:
                    break

                for volume in volumes:
                    if volume.volume_number == "":
                        continue

                    if not chapter_support_toggle and volume.file_type == "chapter":
                        continue

                    lower_name = volume.name.lower()

                    is_digital_comp = "digital" in lower_name and (
                        "compilation" in lower_name or "danke-repack" in lower_name
                    )

                    if (
                        volume.file_type == "chapter"
                        or is_digital_comp
                        or "scan" in lower_name
                        or "c2c" in lower_name
                    ) and volume.extension == ".cbz":
                        print(f"\n{'-' * 80}")
                        print(f"File: {volume.name}")
                        print("-" * 80)

                        if skip_comic_info:
                            # Check if ComicInfo.xml exists and skip if it does
                            comic_info_contents = get_comic_info_xml(volume.path)
                            if comic_info_contents and (
                                "<Title>Chapter" in comic_info_contents
                                or volume.file_type != "chapter"
                            ):
                                print("\tComicInfo.xml found, skipping...")
                                continue

                        title = None

                        if volume.volume_number == "":
                            continue

                        title = f"{volume.file_type.capitalize()}"

                        if isinstance(volume.volume_number, list):
                            lowest, highest = min(volume.volume_number), max(
                                volume.volume_number
                            )
                            title += (
                                f"s {lowest}-{highest}"
                                if lowest != highest
                                else f" {lowest}"
                            )
                        else:
                            title += f" {volume.volume_number}"
                            if volume.volume_part:
                                title += f" Part {volume.volume_part}"

                        if title:
                            print(f"Title: {title}")
                            # Get metadata from CBZ file
                            data = get_cbz_metadata(volume.path)

                            if data and data.title != title:
                                print(f"Data Title: {data.title}")
                                formatted_title = re.sub(r"([,=])", r"^\1", title)

                                # Update metadata using ComicTagger
                                update_metadata(
                                    "comictagger",
                                    volume.path,
                                    [data.title],
                                    [f"title={formatted_title}"],
                                    "CBZ Archive",
                                    "-s -t cr -m",
                                    skip_print=manualmetadata == False,
                                    cbz=True,
                                )
                        continue

                    if (
                        skip_non_digital_manga
                        and volume.extension == ".cbz"
                        and "(digital" not in lower_name
                    ):
                        continue

                    print(
                        f"\n{'-' * 80}\nFile: {os.path.basename(volume.name)}\n{'-' * 80}"
                    )

                    # Process the file
                    process_result = process_file(volume, volumes, file_only=file)

                    if file:
                        stop = True
                        break

                # clear the lru_cache for get_title_from_description()
                get_title_from_description.cache_clear()
