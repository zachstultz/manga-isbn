import cv2
import pytesseract
import regex as re
import urllib.request
import json
import argparse
import zipfile
import os
import string
import subprocess
import sys
import io
import numpy as np
import time
import concurrent.futures
import requests
import html
import difflib as dl
import scandir
import random
import calendar
import langcodes
import socket
import translators as ts
import anilist
import nltk
import xml.etree.ElementTree as ET
from difflib import SequenceMatcher
from skimage.metrics import structural_similarity as ssim
from datetime import datetime
from PIL import Image
from zipfile import BadZipFile
from titlecase import titlecase
from langcodes import *
from functools import partial
from bs4 import BeautifulSoup, SoupStrainer
from discord_webhook import DiscordWebhook
from langdetect import detect
from nltk.tokenize import sent_tokenize
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager
from selenium.webdriver.common.by import By
from math import log10, sqrt
from simyan.comicvine import Comicvine
from simyan.sqlite_cache import SQLiteCache
from simyan.comicvine import Comicvine, ComicvineResource
from lxml import etree

# Version: 1.01

# RUN THESE INSTALLS FOR THE PROGRAM TO WORK PROPERLY!
# sudo apt-get update && sudo pip3 install comictagger[all] && sudo apt-get install calibre && sudo apt-get install wget && sudo -v && wget -nv -O- https://download.calibre-ebook.com/linux-installer.sh | sudo sh /dev/stdin && sudo apt-get install tesseract-ocr

# REQUIRES CHROME TO BE INSTALLED!
# wget https://dl.google.com/linux/direct/google-chrome-stable_current_amd64.deb && sudo apt install ./google-chrome-stable_current_amd64.deb && pip3 install webdriver-manager && pip3 install regex && pip3 install bs4 && pip3 install selenium && rm google-chrome-stable_current_amd64.deb

# downoads required items for nltk.tokenize
nltk.download("punkt")
# The root direcotry for saving of images
ROOT_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "logs")
# Accepted internal zip image extensions
image_extensions = ["jpg", "jpeg", "png", "tbn", "jxl"]
# Accepted files when os.walk is used
# accepted_file_types = ["cbz", "epub"]
accepted_file_types = ["epub", "cbz"]
# The internal extenions that will be checked when looking for the isbn
# in an epub file.
internal_epub_extensions = ["xhtml", "opf", "ncx", "xml", "html"]
# manual title extraction approval
manual_title_approval = False
# If enabled, the user will be prompted before metadata is written to the file
# Otherwise if False, data is written automatically
manual_metadata_write_approval = False
# whether or not the extracted text that the isbn came from
# should be printed out alongside the result
print_extracted_texts_with_result = False
# whether or not to write the results to the file
# False for testing purposes, default is True
write_metadata_to_file = True
# Skips finding the isbn internally and matches to api via image comparision.
only_image_comparision = False
# Whether or not to skip the google_api search + image comparision
skip_image_comparison = False
# whether or not to sleep at certain intervals to avoid api rate limiting
api_rate_limit = True
# Restricts the google search to one or two searches (haven't decided how restrictive yet)
limit_google_search = False
# Whether or not to apply multi-processing when processing image_links
multi_process_image_links = False
# Whether or not to process multiple cbz/epub files at once.
multi_process_files = False
# Whether or not to apply multi-processing when pulling descriptions from a file list of epubs
multi_process_pulling_descriptions = True
# if we should skip letters A-#
skip_letters = False
# The letters that our dirs are allowed to begin with, aka, skip directly to M-Z dirs within the root.
accepted_letters = "[I-Z]"
# Will skip the current file if an isbn is found within the zip comment.
# Useful when wanting to retest only files that don't have a set isbn.
skip_file_if_isbn_in_zip_comment = False
# Useful for tagging remaining cbzs that comictagger couldn't match,
# or haven't been user-submitted to comic-vine yet.
skip_if_file_contains_comic_info = False
# skips all files that were not tagged by comictagger. Useful for tagging remaining cbzs that couldn't get a match
# and still have leftover comictagger metadata.
skip_all_non_comic_tagger_tagged = False
# When enabled, is_ebook=True will not be required for square-enix
# matches. Square-enix releases are not released digitally on google-books.
# Paperback metadata will be used.
square_enix_bypass = True
# Whether or not to scrape google
scrape_google = True
# Whether or not to scrape kobo books
scrape_kobo = False
# Whether or not to scrape bookwalker
scrape_bookwalker = True
# Whether or not to scrape barnes and noble
scrape_barnes_and_noble = True
# Whether or not to scrape comic vine
scrape_comic_vine = True
# Comic Vine API Key
comic_vine_api_key = ""
# skips any volume number that isn't one
skip_non_volume_ones = False
# the amount of time to sleep for when the api hits the rate limit in seconds
sleep_time = 35
# The amount of time to sleep when a limit is hit when webscraping
web_scrape_sleep_time = 5
# The amount of time to sleep inbetween comic vine results.
# Maximum of 200 API hits per hour per category.
comic_vine_sleep_time = 36
# the isbn-13 regex used throughout the program
isbn_13_regex = "(9([-_. :]+)?7([-_. :]+)?(8|9)(([-_. :]+)?[0-9]){10})"
# Our ignored folder names
ignored_folder_names = [
    "Test",
    "Fairy Tail",
    "Gintama",
    "Can Someone Please Explain What's Going On",
    "Future Diary",
]
# Keeps track of the total cbz/epub files encountered
total_files = 0
# The files we wrote metadata to
items_changed = []
# Any errors encountered
errors = []
# Successfull isbn retrievals
successful_isbn_retrievals = []
# Unsuccessful isbn retrievals
unsuccessful_isbn_retrievals = []
# Successfull google api matches
successful_api_matches = []
# Unsuccessful google api matches
unsuccessful_api_matches = []
# Epubs where we couldn't find an isbn, but our second attempt was successful
# The second attempt being an OCR on all the inner images
items_found_through_ocr_on_epub = []
# items that failed an api match through string search and image comparision
items_not_found_through_image_comparision_search = []
# the amount of api hits for the current session
api_hits = 0
# the total amount of retries for an api request
total_api_re_attempts = 10
# required image similarity score for image similarity
required_image_ssim_score = 0.60
# the required mse score to indicate a good match
required_image_mse_score = 0.37
# The required string similarity score using similar method
required_similarity_score = 0.97
# used when checking for a match to anilist
sentence_similarity_score = 0.85
# The discord webhook url for notifications about changes and errors.
discord_webhook_url = []
# Skips novels with a summary, aka skips novels that already have metadata.
skip_novels_with_metadata = False
# Whether or not to log to various files for various reasons
log_to_file = True
# Skips volumes that are older than the set time in minutes.
skip_volumes_older_than_x_time = False
# skips any volume comment that already contains an anilist_id
skip_volume_if_already_has_anilist_id = False
# whether or not to translate title names to improve matching when
# matching to anilist
translate_titles = False
# the cache for series_id results to avoid unncessary api hits
series_ids_cache = []
# True = image similarity uses internal file cover
# False = image similarity uses external file cover
use_internal_cover = True

# Skips any files that were tagged by google books
skip_google_metadata = False

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
        "-sviahai",
        "--skip_volume_if_already_has_anilist_id",
        help="If enabled, the program will skip volumes that already have an anilist id.",
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
    return parser


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
        genres=[],
        tags=[],
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
        self.preview_link = (preview_link,)
        self.image_links = image_links
        self.part = part
        self.series_id = series_id
        self.average_rating = average_rating
        self.is_ebook = is_ebook
        self.api_link = api_link
        self.maturity_rating = maturity_rating
        self.for_sale = for_sale
        self.genres = genres
        self.tags = tags


class Series_Page_Result:
    def __init__(self, series_id, series_name, results, api_results):
        self.series_id = series_id
        self.series_name = series_name
        self.results = results
        self.api_results = api_results


# Clas to store the result
class Result:
    def __init__(self, book, extracted_texts):
        self.book = book
        self.extracted_texts = extracted_texts


class Provider:
    def __init__(self, name, enabled, priority_number):
        self.name = name
        self.enabled = enabled
        self.priority_number = priority_number


# our current list of supported metadata providers
providers = [
    Provider("google", True, 1),
    Provider("bookwalker", True, 2),
    Provider("kobo", False, 3),
    Provider("barnes_and_noble", True, 4),
    Provider("comic_vine", True, 5),
]

# order providers by priority, lowest number first
providers.sort(key=lambda x: x.priority_number)

# Appends, sends, and prints our error message
def send_error_message(error, discord=True):
    print(error)
    if discord != False:
        send_discord_message(error)
    errors.append(error)
    write_to_file("errors.txt", error)


# Appends, sends, and prints our change message
def send_change_message(message):
    print(message)
    send_discord_message(message)
    items_changed.append(message)
    write_to_file("changes.txt", message)


# Sends a discord message using the users webhook url
def send_discord_message(message):
    try:
        if discord_webhook_url:
            webhook = DiscordWebhook(
                url=random.choice(discord_webhook_url),
                content=message,
                rate_limit_retry=True,
            )
            webhook.execute()
    except TypeError as e:
        send_error_message(e, discord=False)


# execute command with subprocess and reutrn the output
def execute_command(command):
    try:
        process = subprocess.Popen(command, stdout=subprocess.PIPE)
        output, error = process.communicate()
        return output.decode("utf-8")
    except Exception as e:
        send_error_message(e)


# prints our ocr extracted texts
def print_extracted_texts(extracted_texts, seperated=False):
    if seperated:
        print(
            "\n--------------------------------[Extracted Texts]--------------------------------"
        )
        for text in extracted_texts:
            print(text)
        print(
            "--------------------------------------------------------------------------------"
        )
    else:
        print(
            "\n--------------------------------[Extracted Texts]--------------------------------"
        )
        print(extracted_texts)
        print(
            "--------------------------------------------------------------------------------"
        )


def remove_tuples_from_results(results):
    for result in results:
        index = results.index(result)
        results[index] = [t for t in result if t]
    return results


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
    keywords_lined_regex = "(EBOOK|MOBI|EPUB|APP|PDF|PAPERBACK)"
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
                        text = re.sub(r"[^0-9]+", "", text, flags=re.IGNORECASE).strip()
                        result = google_api_isbn_lookup(text, file)
                        if result:
                            return result
    return None


# Return the zip comment for the passed zip file
def get_zip_comment(zip_file):
    try:
        with zipfile.ZipFile(zip_file, "r") as zip_ref:
            if zip_ref.comment:
                return zip_ref.comment.decode("utf-8")
            else:
                return ""
    except Exception as e:
        send_error_message(str(e))
        send_error_message("\tFailed to get zip comment for: " + zip_file)
        write_to_file("errors.txt", str(e))
        exc_type, exc_obj, exc_tb = sys.exc_info()
        fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
        print(exc_type, fname, exc_tb.tb_lineno)
        return ""


# Append the passed string to the zip file's comment, seperated by a comma
def append_to_zip_comment(zip_file, string):
    with zipfile.ZipFile(zip_file, "a") as zip_ref:
        zip_ref.comment = zip_ref.comment + f",{string}".encode("utf-8")
    # check that the comment was appended
    with zipfile.ZipFile(zip_file, "r") as zip_ref:
        if string in zip_ref.comment.decode("utf-8"):
            return True
        else:
            return False


# Write the passed string to the zip file's comment
def write_zip_comment(zip_file, comment):
    with zipfile.ZipFile(zip_file, "a") as zip_ref:
        zip_ref.comment = comment.encode("utf-8")
    # check that the comment was written
    with zipfile.ZipFile(zip_file, "r") as zip_ref:
        if comment in zip_ref.comment.decode("utf-8"):
            return True
        else:
            return False


# Prints our results for the user
def print_result(result):
    if hasattr(result, "book"):
        if result.book:
            print(
                "\n--------------------------------[Book Information]------------------------------"
            )
            # get list of all attributes from book Class
            attributes = [
                attr
                for attr in dir(result.book)
                if not callable(getattr(result.book, attr))
            ]
            # remove system attributes
            attributes = [attr for attr in attributes if not attr.startswith("__")]
            # print all attributes
            for attr in attributes:
                # if the value isn't empty
                if getattr(result.book, attr):
                    # titlecase the attribute
                    capitalized = titlecase(attr)
                    print(f"\t{capitalized}: {getattr(result.book, attr)}")
            print(
                "--------------------------------------------------------------------------------\n"
            )
    if (
        print_extracted_texts_with_result
        and hasattr(result, "extracted_texts")
        and result.extracted_texts
    ):
        print_extracted_texts(result.extracted_texts)


# Removes the formatting from the passed string
def remove_formatting(text):
    return re.sub(r"\s+", " ", text, flags=re.IGNORECASE).strip()


# Extracts the text from the image
# Credit to https://www.geeksforgeeks.org/text-detection-and-extraction-using-opencv-and-ocr/
# Modified by me
def extract_texts_from_image(image_path):
    try:
        image_path = cv2.imread(image_path)
        gray = cv2.cvtColor(image_path, cv2.COLOR_BGR2GRAY)
        ret, thresh1 = cv2.threshold(
            gray, 0, 255, cv2.THRESH_OTSU | cv2.THRESH_BINARY_INV
        )
        rect_kernel = cv2.getStructuringElement(cv2.MORPH_RECT, (18, 18))
        dilation = cv2.dilate(thresh1, rect_kernel, iterations=1)
        contours, hierarchy = cv2.findContours(
            dilation, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_NONE
        )
        im2 = image_path.copy()
        extracted_texts = []
        for cnt in contours:
            x, y, w, h = cv2.boundingRect(cnt)
            rect = cv2.rectangle(im2, (x, y), (x + w, y + h), (0, 255, 0), 2)
            cropped = im2[y : y + h, x : x + w]
            text = pytesseract.image_to_string(cropped)
            if text != "":
                extracted_texts.append(text)
        # join all of the text lines together
        extracted_texts = " ".join(extracted_texts)
        return extracted_texts
    except Exception as e:
        send_error_message(str(e) + ": " + str(root))
        write_to_file("isbn_script_errors.txt", str(e))
        exc_type, exc_obj, exc_tb = sys.exc_info()
        fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
        print(exc_type, fname, exc_tb.tb_lineno)
        return []


def remove_all_alphabetical_characters(text):
    for char in text:
        if char.isalpha():
            text = text.replace(char, "")
    return text


def search_for_text(text, file):
    find_all_result = find_all_searches(text, file)
    if find_all_result:
        return find_all_result
    else:
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
                        api_result = google_api_isbn_lookup(t, file)
                        if api_result:
                            return api_result
            results = None
    return results


# Searches the extracted text for the ISBN number
def isbn_search(text, file):
    all_unmodified_search = search_for_text(text, file)
    if all_unmodified_search:
        return all_unmodified_search
    lines = []
    # split into lines on \n
    lines = text.split("\n")
    # remove empty lines
    lines = [line for line in lines if line.strip()]
    for line in lines:
        # combine the current line and the previous line, if it's not the first in array
        combined = ""
        if lines.index(line) > 0:
            combined = lines[lines.index(line) - 1] + " " + line
            combined_two = lines[lines.index(line) - 1] + line
            combined_search = search_for_text(combined, file)
            if combined_search:
                return combined_search
            combined_search_two = search_for_text(combined_two, file)
            if combined_search_two:
                return combined_search_two
        else:
            individual_line_serach = search_for_text(line, file)
            if individual_line_serach:
                return individual_line_serach
    # join all lines and search
    # joined = " ".join(lines)
    # all_joined_search = search_for_text(joined, file)
    # if all_joined_search:
    #    return all_joined_search
    return None


# Searches for the IBSN number within the extracted texts
def search_for_isbn(extracted_texts, file):
    book = isbn_search(extracted_texts, file)
    if book:
        return book
    else:
        return False


# Retrieves the series name through various regexes
# Removes the volume number and anything to the right of it, and strips it.
def get_series_name_from_file_name(name):
    name = (
        re.sub(
            r"(\b|\s)((\s|)-(\s|)|)(Part|)(\[|\(|\{)?(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)(\.|)([-_. ]|)([0-9]+)(\b|\s).*",
            "",
            name,
            flags=re.IGNORECASE,
        )
    ).strip()
    # if name ends with , remove it
    name = re.sub(r"(\,|\.|\:)$", "", name)
    name = re.sub(r"(.epub|.cbz)", "", name, flags=re.IGNORECASE).strip()
    return name


def check_for_multi_volume_file(file_name):
    if re.search(
        r"(\b(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)(\.)?(\s+)?([0-9]+(\.[0-9]+)?)([-_]([0-9]+(\.[0-9]+)?))+\b)",
        remove_bracketed_info_from_name(file_name),
        re.IGNORECASE,
    ):
        return True
    else:
        return False


def convert_list_of_numbers_to_array(string):
    numbers = []
    numbers_search = re.sub(r"[-_]", " ", string)
    numbers_search = remove_dual_space(numbers_search).strip()
    numbers_search = numbers_search.split(" ")
    # convert them to numbers using set_num_as_float_or_int
    numbers_search = [set_num_as_float_or_int(num) for num in numbers_search]
    if numbers_search:
        # get lowest number in list
        lowest_number = min(numbers_search)
        # get highest number in list
        highest_number = max(numbers_search)
        # discard any numbers inbetween the lowest and highest number
        if lowest_number and highest_number:
            numbers = [lowest_number, highest_number]
        elif lowest_number and not highest_number:
            numbers = [lowest_number]
        elif highest_number and not lowest_number:
            numbers = [highest_number]
    return numbers


# Finds the volume number and strips out everything except that number
def remove_everything_but_volume_num(files):
    results = []
    is_multi_volume = False
    for file in files[:]:
        is_multi_volume = check_for_multi_volume_file(file)
        result = re.search(
            r"\b(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)((\.)|)(\s+)?([0-9]+)(([-_.])([0-9]+)|)+\b",
            file,
            re.IGNORECASE,
        )
        if result:
            try:
                file = result
                if hasattr(file, "group"):
                    file = file.group()
                else:
                    file = ""
                file = re.sub(
                    r"\b(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)(\.|)([-_. ])?",
                    "",
                    file,
                    flags=re.IGNORECASE,
                ).strip()
                if re.search(
                    r"\b[0-9]+(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)[0-9]+\b",
                    file,
                    re.IGNORECASE,
                ):
                    file = (
                        re.sub(
                            r"(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)",
                            ".",
                            file,
                            flags=re.IGNORECASE,
                        )
                    ).strip()
                try:
                    if is_multi_volume:
                        volume_numbers = convert_list_of_numbers_to_array(file)
                        if volume_numbers:
                            if len(volume_numbers) > 1:
                                for volume_number in volume_numbers:
                                    results.append(float(volume_number))
                            elif len(volume_numbers) == 1:
                                results.append(float(volume_numbers[0]))
                                is_multi_volume = False
                    else:
                        results.append(float(file))
                except ValueError:
                    message = "Not a float: " + files[0]
                    print(message)
                    write_to_file("errors.txt", message)
            except AttributeError:
                print(str(AttributeError.with_traceback))
        else:
            files.remove(file)
    if is_multi_volume == True and len(results) != 0:
        return results
    elif len(results) != 0 and (len(results) == len(files)):
        return results[0]
    elif len(results) == 0:
        return ""


# get the title from the description
def get_title_from_description(description):
    search = re.search(
        r"(^([\"\“]?[A-Z]+([0-9]+|[^A-Za-z0-9]+)([0-9]+)?)+)", description
    )
    if search:
        search = search.group(0).strip()
        # search = re.sub(r"(^[\"\“])", "", search)
        # search = re.sub(r"([\"\“\”]$)", "", search).strip()
        search = re.sub(r"\s[A-Z]?[^A-Za-z0-9]?$", "", search).strip()
        search = remove_dual_space(search).strip()
        search = re.sub(r"([A-Z])(\.$)", r"\1", search).strip()
        word_list = search.split()
        number_of_words = len(word_list)
        if len(search) > 3 and number_of_words >= 2:
            return search
        else:
            None
    else:
        return None


attempts = 1


def set_num_as_float_or_int(volume_number):
    try:
        if volume_number != "":
            # if re search for \xbd or ½, repalce it with 0.5
            if re.search(r"(\xbd)", str(volume_number)) or re.search(
                r"(½)", str(volume_number)
            ):
                volume_number = re.sub(r"(\xbd)", "0.5", str(volume_number))
                volume_number = re.sub(r"(½)", "0.5", str(volume_number))
            if isinstance(volume_number, list):
                result = ""
                for num in volume_number:
                    if float(num) == int(num):
                        if num == volume_number[-1]:
                            result += str(int(num))
                        else:
                            result += str(int(num)) + "-"
                    else:
                        if num == volume_number[-1]:
                            result += str(float(num))
                        else:
                            result += str(float(num)) + "-"
                return result
            elif isinstance(volume_number, str) and re.search(r"\.", volume_number):
                volume_number = float(volume_number)
            else:
                if float(volume_number) == int(volume_number):
                    volume_number = int(volume_number)
                else:
                    volume_number = float(volume_number)
    except Exception as e:
        send_error_message(
            "\tFailed to convert volume number to float or int: " + str(volume_number)
        )
        send_error_message("\t" + str(e))
        return ""
    return volume_number


# Removes any unaccepted file types
def remove_unaccepted_file_types(files, root):
    for file in files[:]:
        extension = re.sub("\.", "", get_file_extension(file))
        if extension not in accepted_file_types and os.path.isfile(
            os.path.join(root, file)
        ):
            files.remove(file)


# Removes all chapter releases
def remove_all_chapters(files):
    for file in files[:]:
        if contains_chapter_keywords(file) and not contains_volume_keywords(file):
            files.remove(file)


# Cleans up the files array before usage
def clean_and_sort(root, files=None, dirs=None, sort=False):
    if files:
        if sort:
            files.sort()
        files = remove_hidden_files(files)
        remove_unaccepted_file_types(files, root)
        remove_all_chapters(files)
    if dirs:
        if sort:
            dirs.sort()
        dirs = remove_hidden_folders(dirs)
        remove_ignored_folders(dirs)


def contains_volume_keywords(file):
    return re.search(
        r"((\s(\s-\s|)(Part|)+(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)(\.|)([-_. ]|)([0-9]+)\b)|\s(\s-\s|)(Part|)(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)(\.|)([-_. ]|)([0-9]+)([-_.])(\s-\s|)(Part|)(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)([0-9]+)\s|\s(\s-\s|)(Part|)(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)(\.|)([-_. ]|)([0-9]+)([-_.])(\s-\s|)(Part|)(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)([0-9]+)\s)",
        file,
        re.IGNORECASE,
    )


# check if volume file name is a chapter
def contains_chapter_keywords(file_name):
    return re.search(
        r"\b((ch|c|d|chapter|chap)([-_. ](\s|)|)|)(\d)+(([.](\d)+)?)(([-_. ](\s|)|)|)(\d)+(([.](\d)+)?)(\s|(.cbz)?(.epub)?)",
        file_name,
        re.IGNORECASE,
    )


# Checks for volume keywords and chapter keywords.
# If neither are present, the volume is assumed to be a one-shot volume.
def is_one_shot(file_name, root):
    files = os.listdir(root)
    clean_and_sort(root, files)
    continue_logic = False
    if len(files) == 1:
        continue_logic = True
    if continue_logic == True:
        volume_file_status = contains_volume_keywords(file_name)
        chapter_file_status = contains_chapter_keywords(file_name)
        if not volume_file_status and not chapter_file_status:
            return True
    return False


# Returns an extensionless name
def get_extensionless_name(file):
    return os.path.splitext(file)[0]


# only print the difference betwen the two strings
def print_diff(s1, s2):
    seq_matcher = dl.SequenceMatcher(None, s1, s2)
    print("\n\t-------------Summary Differences-------------")
    for tag, i1, i2, j1, j2 in seq_matcher.get_opcodes():
        print(
            f"\t\t{tag:7} s1[{i1}:{i2}] --> s2[{j1}:{j2}] {s1[i1:i2]!r:>6} --> {s2[j1:j2]!r}\n"
        )
    print("\t-----------------------------------------------")


# convert array of numbers, to a string, with each number separated by a dash
def convert_array_to_string_with_dashes(array):
    result = ""
    for num in array:
        if num == array[-1]:
            result += str(num)
        else:
            result += str(num) + "-"
    return result


# Looks up the IBSN number on Google Books API and returns the information
def google_api_isbn_lookup(
    isbn,
    file_name,
    text_search=None,
    skip_title_check=False,
    max_results_num=15,
    in_line_search=False,
    type=None,
    number=None,
    volume_id=None,
    quoted_search=None,
):
    global attempts
    global sleep_time
    global api_hits
    file_dir = os.path.dirname(file_name)
    file_name = os.path.basename(file_name)
    original_file_name = file_name
    extension = get_file_extension(original_file_name)
    file_dir_files = []
    try:
        base_api_link = ""
        text = ""
        if text_search:
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
            if in_line_search:
                word = get_search_keyword(
                    re.sub(
                        r"[^A-Za-z0-9\s]",
                        "",
                        remove_punctuation(
                            get_series_name_from_file_name(
                                re.sub(r"[\-\_]", " ", file_name, flags=re.IGNORECASE)
                            )
                        ),
                    )
                )
                if word:
                    base_api_link += "+intitle:" + word
            elif number:
                if isinstance(number, list):
                    base_api_link += "+intitle:" + str(number[0])
                else:
                    base_api_link += "+intitle:" + str(number)
            # prevents "The Case Files of Jeweler Richard" light novel from being found.
            # if extension == "epub":
            #     base_api_link += "&download=epub"
            base_api_link = (
                base_api_link
                + "&maxResults="
                + str(max_results_num)
                + "&printType=books"
                + '&langRestrict="en"'
            )
            print("Search: " + base_api_link)
            with urllib.request.urlopen(base_api_link) as f:
                text = f.read()
        elif volume_id:
            base_api_link = "https://www.googleapis.com/books/v1/volumes/"
            with urllib.request.urlopen(base_api_link + volume_id) as f:
                text = f.read()
        else:
            base_api_link = "https://www.googleapis.com/books/v1/volumes?q=isbn:"
            with urllib.request.urlopen(base_api_link + isbn) as f:
                text = f.read()
        if text:
            decoded_text = text.decode("utf-8")
            obj = json.loads(decoded_text)
            if obj:
                items = []
                if not volume_id:
                    if obj["totalItems"] > 0:
                        items = obj["items"]
                    else:
                        items = []
                else:
                    if obj:
                        items = [obj]
                    else:
                        items = []
                if text_search:
                    if len(items) > 1:
                        api_hits += len(items)
                    else:
                        api_hits += 1
                else:
                    api_hits += 1
                if api_rate_limit:
                    if api_hits % 25 == 0:
                        print("\n\tAPI Hits: " + str(api_hits))
                        print(
                            "\tSleeping for "
                            + str(sleep_time)
                            + " seconds to avoid being api-rate limited.\n"
                        )
                        time.sleep(sleep_time)
                books = []
                for_sale = ""
                for item in items:
                    if "saleInfo" in item:
                        if "isEbook" in item["saleInfo"]:
                            is_ebook = item["saleInfo"]["isEbook"]
                        else:
                            is_ebook = ""
                        if "saleability" in item["saleInfo"]:
                            for_sale = item["saleInfo"]["saleability"]
                        else:
                            for_sale = ""
                    else:
                        is_ebook = ""
                    if text_search or volume_id:
                        isbn = 0
                        if "title" in item["volumeInfo"]:
                            file_name = item["volumeInfo"]["title"]
                    part = get_volume_part(file_name)
                    if part:
                        part = set_num_as_float_or_int(part)
                    else:
                        part = ""
                    id = ""
                    if "id" in item:
                        id = item["id"]
                    volume_info = item["volumeInfo"]
                    if "seriesInfo" in volume_info:
                        series_info = volume_info["seriesInfo"]
                        if "volumeSeries" in series_info:
                            volume_series = series_info["volumeSeries"]
                            if len(volume_series) > 0:
                                series_id = volume_series[0]
                                if "seriesId" in series_id:
                                    series_id = series_id["seriesId"]
                                    series_id = "series_id:" + series_id
                                else:
                                    series_id = "series_id:NONE"
                            else:
                                series_id = "series_id:NONE"
                        else:
                            series_id = "series_id:NONE"
                    else:
                        series_id = "series_id:NONE"
                    if "maturityRating" in volume_info:
                        maturity_rating = volume_info["maturityRating"]
                    else:
                        maturity_rating = ""
                    if "description" in volume_info:
                        summary = volume_info["description"]
                        # unescape the summary
                        summary = re.sub(r"\u200b", "", summary)
                        summary = html.unescape(summary)
                        # remove all html tags from the summary
                        # 'ANSWERS<br><br> What makes a Reaper?'
                        if re.search(r"([a-z])(<br>)+([A-Z])", summary):
                            summary = re.sub(
                                r"([a-z])(<br>)+([A-Z])", r"\1. \3", summary
                            )
                        if re.search(r"<[^>]*>", summary):
                            summary = re.sub(r"<[^>]*>", " ", summary)
                        if re.search(r"(\s+)([\!\.\?])$", summary, re.IGNORECASE):
                            summary = re.sub(r"(\s+)([\!\.\?])$", r"\2", summary)
                        summary = remove_dual_space(summary).strip()
                        if re.search(r"(\s+)([\.\!\?]$)", summary):
                            summary = re.sub(
                                r"(\s+)([\.\!\?]$)", r"\2", summary
                            ).strip()
                        # if summary has a period,exclamation, or questoin mark right next to a capital letter, put a space after the punctuation
                        # DO NOT IGNORECASE
                        if re.search(r"([\.\!\?])([A-Z][a-zA-Z])", summary):
                            summary = re.sub(
                                r"([\.\!\?])\s*([A-Z]([a-zA-Z]))", r"\1 \2", summary
                            ).strip()
                        # Combat . Between --> Combat. Between
                        if re.search(r"([a-z])(\s+)([\.!?,])", summary):
                            summary = re.sub(
                                r"([a-z])(\s+)([\.!?,])", r"\1\3", summary
                            ).strip()
                        # " Accelerator --> "Accelerator
                        if re.search(r"(\")(\s+)([A-Z])", summary):
                            summary = re.sub(r"(\")(\s+)([A-Z])", r"\1\3", summary)
                        if re.search(r"([A-Z\.\!\?])(\")", summary) and not re.search(
                            r"(([A-Z\.\!\?])(\"))$", summary
                        ):
                            summary = re.sub(r"([A-Z\.\!\?])(\")", r"\1 \2", summary)
                    else:
                        summary = ""
                    volume_number = remove_everything_but_volume_num([file_name])
                    if not volume_number:
                        one_shot = is_one_shot(file_name, root)
                        if one_shot:
                            volume_number = 1
                    elif not isinstance(volume_number, list):
                        volume_number = set_num_as_float_or_int(volume_number)
                    else:
                        volume_number = [
                            set_num_as_float_or_int(x) for x in volume_number
                        ]
                    api_link = ""
                    if text_search or volume_id:
                        if "industryIdentifiers" in volume_info:
                            identifiers = volume_info["industryIdentifiers"]
                            for identifier in identifiers:
                                if identifier["type"] == "ISBN_13":
                                    isbn = identifier["identifier"]
                                    if isbn and not volume_id:
                                        api_link = (
                                            "https://www.googleapis.com/books/v1/volumes?q=isbn:"
                                            + str(isbn)
                                        )
                                    else:
                                        api_link = ""
                                    break
                                elif identifier["type"] == "OTHER":
                                    possible_result = identifier["identifier"]
                                    search_result = re.search(
                                        rf"{isbn_13_regex}",
                                        possible_result,
                                        re.IGNORECASE,
                                    )
                                    if search_result:
                                        isbn = search_result.group(0)
                                        if isbn and not volume_id:
                                            api_link = (
                                                "https://www.googleapis.com/books/v1/volumes?q=isbn:"
                                                + str(isbn)
                                            )
                                        else:
                                            api_link = ""
                                        break
                                else:
                                    api_link = ""
                    elif (
                        (not text_search and not volume_id)
                        and isbn
                        and (isbn != 0 and isbn != "0")
                    ):
                        api_link = (
                            "https://www.googleapis.com/books/v1/volumes?q=isbn:"
                            + str(isbn)
                        )
                    if volume_id:
                        api_link = "https://www.googleapis.com/books/v1/volumes/" + str(
                            volume_id
                        )
                    volume_keyword = ""
                    if isinstance(volume_number, list):
                        volume_keyword = "Volumes "
                    else:
                        volume_keyword = "Volume "
                    if "title" in volume_info:
                        if summary != "":
                            search = ""
                            search = get_title_from_description(summary)
                            if search:
                                descriptions = []
                                if os.path.isdir(file_dir):
                                    file_dir_files = os.listdir(file_dir)
                                    file_dir_files = remove_hidden_files(files)
                                    file_dir_files = remove_non_cbz_epub(files)
                                    file_dir_files = [
                                        os.path.join(file_dir, file)
                                        for file in file_dir_files
                                        if file != original_file_name
                                        and file.endswith(".epub")
                                    ]
                                if multi_process_pulling_descriptions:
                                    with concurrent.futures.ThreadPoolExecutor() as executor:
                                        results = executor.map(
                                            get_metadata_from_epub_via_calibre,
                                            file_dir_files,
                                        )
                                        for result in results:
                                            if result.comments:
                                                descriptions.append(result.comments)
                                else:
                                    for f in file_dir_files:
                                        descriptions.append(
                                            get_metadata_from_epub_via_calibre(
                                                os.path.join(file_dir, f)
                                            ).comments
                                        )
                                found = False
                                for desc in descriptions:
                                    if re.search(search, desc, flags=re.IGNORECASE):
                                        found = True
                                        break
                                if search and not found:
                                    message = (
                                        search
                                        + " from "
                                        + str(isbn)
                                        + " and from file: "
                                        + file_name
                                    )
                                    if not text_search:
                                        write_to_file(
                                            "extracted_titles.txt",
                                            message,
                                            without_date=True,
                                        )
                                    title = titlecase(search)
                                    if manual_title_approval and not skip_title_check:
                                        print(
                                            "\n--------------------------------Title Extraction Check--------------------------------"
                                        )
                                        print("\n\tSummary: " + summary)
                                        print("\n\tTitle: " + titlecase(search))
                                        user_input = input(
                                            "\n\tIs this title correct? (y/n/i): "
                                        )
                                        print(
                                            "-------------------------------------------------------------------------------------"
                                        )
                                        if user_input == "y":
                                            title = titlecase(search)
                                        elif user_input == "i":
                                            title = input("\n\tEnter title: ")
                                            title = titlecase(title)
                                        else:
                                            if not isinstance(volume_number, list):
                                                title = volume_keyword + str(
                                                    volume_number
                                                )
                                            else:
                                                title = volume_keyword + str(
                                                    convert_array_to_string_with_dashes(
                                                        volume_number
                                                    )
                                                )
                                            if part:
                                                title += " Part " + str(part)
                                else:
                                    if not isinstance(volume_number, list):
                                        title = volume_keyword + str(volume_number)
                                    else:
                                        title = volume_keyword + str(
                                            convert_array_to_string_with_dashes(
                                                volume_number
                                            )
                                        )
                                    if part:
                                        title += " Part " + str(part)
                            else:
                                if not isinstance(volume_number, list):
                                    title = volume_keyword + str(volume_number)
                                else:
                                    title = volume_keyword + str(
                                        convert_array_to_string_with_dashes(
                                            volume_number
                                        )
                                    )
                                if part:
                                    title += " Part " + str(part)
                        else:
                            if not isinstance(volume_number, list):
                                title = volume_keyword + str(volume_number)
                            else:
                                title = volume_keyword + str(
                                    convert_array_to_string_with_dashes(volume_number)
                                )
                            if part:
                                title += " Part " + str(part)
                    else:
                        if not isinstance(volume_number, list):
                            title = volume_keyword + str(volume_number)
                        else:
                            title = volume_keyword + str(
                                convert_array_to_string_with_dashes(volume_number)
                            )
                        if part:
                            title += " Part " + str(part)
                    if not text_search:
                        series = get_series_name_from_file_name(file_name)
                    elif "title" in volume_info:
                        series = str(
                            get_series_name_from_file_name(volume_info["title"])
                        )
                    else:
                        series = ""
                    if "authors" in volume_info:
                        writer = volume_info["authors"]
                        if isinstance(writer, list) and len(writer) > 1:
                            combined = ""
                            for author in writer:
                                # 'Tugikuru Corp.' --> 'Tugikuru Corp'
                                author = re.sub(r"[,.!?]", "", author).strip()
                                # 'Tugikuru Corp (Test)' --> 'Tugikuru Corp'
                                author = re.sub(
                                    r"((\s+)?([\(\{\[])(.*)([\]\}\)])(\s+)?)",
                                    "",
                                    author,
                                ).strip()
                                author = titlecase(author)
                                if author != writer[-1]:
                                    combined += author + ", "
                                else:
                                    combined += author
                            writer = combined
                        elif isinstance(writer, list) and len(writer) == 1:
                            writer = re.sub(r",", "", writer[0]).strip()
                            writer = titlecase(writer)
                        else:
                            writer = ""
                    else:
                        writer = ""
                    if "publisher" in volume_info:
                        publisher = volume_info["publisher"]
                        publisher = re.sub(
                            r"(,\s+|)?((LLC|Inc|\bCo\b).*)",
                            "",
                            publisher,
                            flags=re.IGNORECASE,
                        ).strip()
                        publisher = re.sub(r"[^a-zA-Z0-9\s-,\.]", "", publisher).strip()
                        publisher = titlecase(publisher)
                        if not text_search:
                            write_to_file(
                                "publishers.txt", publisher, without_date=True
                            )
                    else:
                        publisher = ""
                    if "publishedDate" in volume_info:
                        published_date = volume_info["publishedDate"]
                        if published_date != None:
                            year = published_date[0:4]
                            month = published_date[5:7]
                            if month and len(month) == 1:
                                month = "0" + month
                            day = published_date[8:10]
                            if day and len(day) == 1:
                                day = "0" + day
                            published_date = (
                                str(year) + "-" + str(month) + "-" + str(day)
                            )
                            if re.search(r"(-+$)", published_date):
                                published_date = re.sub(
                                    r"(-+$)", "", published_date
                                ).strip()
                        else:
                            published_date = ""
                            year = ""
                            month = ""
                            day = ""
                    else:
                        published_date = ""
                        year = ""
                        month = ""
                        day = ""
                    if "pageCount" in volume_info:
                        page_count = volume_info["pageCount"]
                    else:
                        page_count = ""
                    if "categories" in volume_info:
                        categories = volume_info["categories"]
                    else:
                        categories = ""
                    if "language" in volume_info:
                        language = volume_info["language"]
                        if language:
                            language = standardize_tag(language)
                    else:
                        language = ""
                    if "previewLink" in volume_info:
                        preview_link = volume_info["previewLink"]
                    else:
                        preview_link = ""
                    if "averageRating" in volume_info:
                        average_rating = volume_info["averageRating"]
                        if average_rating:
                            average_rating = set_num_as_float_or_int(average_rating)
                        if average_rating > 5:
                            average_rating = ""
                    else:
                        average_rating = ""
                    image_links = []
                    if "imageLinks" in volume_info:
                        for key, value in volume_info["imageLinks"].items():
                            if len(image_links) == 2:
                                break
                            thumbnail = value
                            if thumbnail not in image_links:
                                thumbnail = re.sub(
                                    r"&edge=curl", "", thumbnail, flags=re.IGNORECASE
                                )
                                image_links.append(thumbnail)
                            # zoom_zero = re.sub(r"zoom=[1-99]", "zoom=0", thumbnail)
                            # if zoom_zero not in image_links:
                            #     image_links.append(zoom_zero)
                            with_width_and_height_adjustment = (
                                thumbnail + "&fife=w800-h1200"
                            )
                            if with_width_and_height_adjustment not in image_links:
                                image_links.append(with_width_and_height_adjustment)
                    else:
                        image_links = ""
                    if isbn == 0:
                        isbn = ""
                    if not api_link:
                        api_link = ""
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
                    )
                    books.append(book)
                if len(books) > 1:
                    if not text_search:
                        return books[0]
                    else:
                        return books
                elif len(books) == 1:
                    return books[0]
                elif len(books) == 0:
                    return None
            else:
                api_hits += 1
                return None
        else:
            api_hits += 1
            return None
    except Exception as e:
        exc_type, exc_obj, exc_tb = sys.exc_info()
        fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
        print(exc_type, fname, exc_tb.tb_lineno)
        return None


# Check the text file line by line for the passed message
def check_text_file_for_message(text_file, message):
    with open(text_file, "r") as f:
        for line in f:
            if message.strip() == line.strip():
                return True
    return False


# Writes a log file
def write_to_file(
    file, message, without_date=False, overwrite=False, check_for_dup=False
):
    if log_to_file:
        message = re.sub("\t|\n", "", str(message), flags=re.IGNORECASE).strip()
        contains = False
        if check_for_dup and os.path.isfile(os.path.join(ROOT_DIR, file)):
            contains = check_text_file_for_message(
                os.path.join(ROOT_DIR, file), message
            )
        if not contains or overwrite:
            try:
                file_path = os.path.join(ROOT_DIR, file)
                append_write = ""
                if os.path.exists(file_path):
                    if not overwrite:
                        append_write = "a"  # append if already exists
                    else:
                        append_write = "w"
                else:
                    append_write = "w"  # make a new file if not
                try:
                    if append_write != "":
                        now = datetime.now()
                        dt_string = now.strftime("%d/%m/%Y %H:%M:%S")
                        file = open(file_path, append_write)
                        if without_date:
                            file.write("\n " + message)
                        else:
                            file.write("\n" + dt_string + " " + message)
                        file.close()
                except Exception as e:
                    send_error_message(e)
            except Exception as e:
                send_error_message(e)


# parse zip file and return the last three images
def parse_zip_file(zip_file):
    paths = []
    with zipfile.ZipFile(zip_file, "r") as zip_ref:
        images = []
        list = zip_ref.namelist()
        for z_file in list:
            extension = os.path.basename(z_file).split(".")[-1]
            if extension in image_extensions:
                images.append(z_file)
        images = remove_hidden_files(images)
        images.sort()
        if zip_file.split(".")[-1] == "cbz":
            # remove the first image from images [first image is usually the cover, so we don't need to scan that]
            # images.pop(0)
            comb = []
            back_images = images[-17:]
            front_images = images[:7]
            front_images.reverse()
            back_images_two = back_images[-2:]
            back_images_two.reverse()
            # add back_images_two to comb
            comb.extend(back_images_two)
            front_images_two = front_images[-2:]
            front_images_two.sort()
            comb.extend(front_images_two)
            # add all images from back_images to comb if they're not already in there
            back_images.reverse()
            front_images.sort()
            for image in back_images:
                if image not in comb:
                    comb.append(image)
            for image in front_images:
                if image not in comb:
                    comb.append(image)
            images = comb
        # save each image in images to ROOT_DIR and append the full paths to paths
        for image in images:
            if not os.path.exists(os.path.join(ROOT_DIR, image)):
                try:
                    zip_ref.extract(image, ROOT_DIR)
                except BadZipFile as e:
                    send_error_message(e)
                    write_to_file("bad_zip_file.txt", zip_file)
                    return None
            paths.append(os.path.join(ROOT_DIR, image))
    return paths


def remove_leftover_images(images):
    for image in images:
        if os.path.isfile(image):
            os.remove(image)
        else:
            send_error_message("\tFile not found: " + image)


# extract text from image using tesseract
def extract_text_from_image(image):
    try:
        img = cv2.imread(image)
        img = cv2.resize(img, None, fx=0.5, fy=0.5)
        gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        new_image = cv2.adaptiveThreshold(
            gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C, cv2.THRESH_BINARY, 85, 11
        )
        text = pytesseract.image_to_string(new_image, config="--psm 3")
        text = pytesseract.image_to_string(image)
        return text
    except Exception as e:
        errors.append("image: " + image + " error: " + str(e))
        send_error_message("Text Extraction Failed: " + image)
        write_to_file("isbn_script_errors.txt", str(e))
        exc_type, exc_obj, exc_tb = sys.exc_info()
        fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
        print(exc_type, fname, exc_tb.tb_lineno)
        return None


def book_stuff(book, zip_file, texts):
    book = book
    if book:
        isbn = ""
        if isinstance(book, list):
            isbn = book[0].isbn
            result = Result(book[0], texts)
        else:
            isbn = book.isbn
            result = Result(book, texts)
        message = (
            "\tSuccessful API Match: "
            + "https://www.googleapis.com/books/v1/volumes?q=isbn:"
            + str(isbn)
        )
        send_change_message(message)
        message = message + " for File: " + os.path.basename(zip_file)
        successful_api_matches.append(zip_file)
        write_to_file("success_api_match.txt", message)
        if result:
            print_result(result)
            return result
        else:
            return None
    else:
        message = (
            "\tUnsuccessful API Match: "
            + os.path.basename(zip_file)
            + " for ISBN:"
            + isbn
        )
        send_error_message(message)
        message = "\tUnsuccessful API Match: " + zip_file + " for " + isbn
        unsuccessful_api_matches.append(zip_file)
        write_to_file("\tFailed_api_match.txt", message)
        return "no_api_match"


def isbn_stuff(extracted_texts, image, zip_file, images, second=False, skip=False):
    book = search_for_isbn(extracted_texts, zip_file)
    if hasattr(book, "isbn"):
        if book.isbn:
            if not skip:
                message = (
                    "\tISBN: " + book.isbn + " found in " + os.path.basename(image)
                )
                send_change_message(message)
            else:
                message = "\tISBN: " + book.isbn + " found in file list."
                send_change_message(message)
            message = "\tISBN: " + book.isbn + " found in " + os.path.basename(zip_file)
            successful_isbn_retrievals.append(zip_file)
            write_to_file("success_isbn_retrievals.txt", message)
            return book
    elif not skip:
        message = "\tNo ISBN found in " + os.path.basename(image)
        print(message)
        if image == images[-1] and second:
            message = "\tNo ISBN found in File: " + os.path.basename(zip_file)
            unsuccessful_isbn_retrievals.append(zip_file)
            write_to_file("no_isbn.txt", message)
            return None


def zip_file_stuff(zip_file, second_attempt=False):
    if not os.path.isfile(zip_file):
        print("File does not exist")
        return
    if not zipfile.is_zipfile(zip_file):
        print("File is not a zip file")
        return
    if second_attempt:
        print("----------------------------------------------------------------")
        print("Second attempt using OCR on images...")
        print("----------------------------------------------------------------")
    extension = get_file_extension(file)
    result = None
    if extension == "cbz" or (extension == "epub" and second_attempt):
        images = parse_zip_file(zip_file)
        if images is None:
            send_error_message("No images found in: " + os.path.basename(zip_file))
            write_to_file("no_images.txt", os.path.basename(zip_file))
            return None
        for image in images:
            if image != "" and image:
                extracted_texts = extract_text_from_image(image)
                if extracted_texts:
                    isbn = isbn_stuff(extracted_texts, image, zip_file, images)
                    if isbn:
                        result = book_stuff(isbn, zip_file, extracted_texts)
                        if result:
                            break
        if not result:
            print(
                "\t--------------------------------Attempting second try with alternative OCR method--------------------------------"
            )
            for image in images:
                if image != "" and image:
                    extracted_texts_two = extract_texts_from_image(image)
                    if extracted_texts_two:
                        isbn = isbn_stuff(
                            extracted_texts_two, image, zip_file, images, second=True
                        )
                        if isbn:
                            result = book_stuff(isbn, zip_file, extracted_texts_two)
                            if result:
                                break
        remove_leftover_images(images)
        if result and result != "no_api_match":
            return result
        else:
            return None
    elif extension == "epub":
        with zipfile.ZipFile(zip_file, "r") as zip_ref:
            list = zip_ref.namelist()
            list_str = str(list)
            for item in list:
                base = os.path.basename(item)
                if base == "content.opf":
                    list.remove(item)
                    list.insert(0, item)
                elif base == "package.opf":
                    list.remove(item)
                    list.insert(1, item)
                elif base == "copyright.xhtml":
                    list.remove(item)
                    list.insert(2, item)
            isbn = isbn_stuff(list_str, zip_file, zip_file, list, skip=True)
            if isbn:
                result = book_stuff(isbn, zip_file, list_str)
                if result:
                    return result
            else:
                for item in list[:]:
                    extension = get_file_extension(item)
                    if not extension in internal_epub_extensions:
                        list.remove(item)
                for f in list:
                    extension = get_file_extension(f)
                    if extension in internal_epub_extensions:
                        text = zip_ref.read(f).decode("utf-8")
                        isbn = isbn_stuff(text, f, zip_file, list)
                        if isbn:
                            result = book_stuff(isbn, zip_file, text)
                            if result:
                                break
        if result:
            return result
        else:
            return None


# Removes any folder names in the ignored_folders
def remove_ignored_folders(dirs):
    if len(ignored_folder_names) != 0:
        dirs[:] = [d for d in dirs if d not in ignored_folder_names]


# Removes hidden folders from the file list
def remove_hidden_folders(dirs):
    return [d for d in dirs if not d.startswith(".")]


# Removes hidden folders from the dirs list
def remove_hidden_files(files):
    for file in files[:]:
        if file.startswith(".") or os.path.basename(file).startswith("."):
            files.remove(file)
    return files


# Get file extension from file name
def get_file_extension(file):
    return file.split(".")[-1]


# Remove all files from the list that don't have an extension of .cbz or .epub
def remove_non_cbz_epub(files):
    for file in files[:]:
        extension = get_file_extension(file)
        if not extension in accepted_file_types:
            files.remove(file)
    return files


# Retrieve isbn from epub file
def get_isbn_from_epub(epub_file):
    with zipfile.ZipFile(epub_file, "r") as zip_ref:
        for file in zip_ref.namelist():
            if file.split(".")[-1] == "opf":
                text = zip_ref.read(file)
                text = text.decode("utf-8")
                book = isbn_search(text, epub_file)
                if book:
                    return book
    return False


# Check epub file for a summary inside of any .opf file, return True if found
def check_epub_for_title(epub_file):
    with zipfile.ZipFile(epub_file, "r") as zip_ref:
        for file in zip_ref.namelist():
            extension = get_file_extension(file)
            if extension == "opf":
                text = zip_ref.read(file)
                text = text.decode("utf-8")
                if re.search(r"((description|summary)>)", text):
                    return True
    return False


# Check zip file for ComicInfo.xml, return True if it exists
def check_for_comic_info_xml(zip_file, book):
    with zipfile.ZipFile(zip_file, "r") as zip_ref:
        list = zip_ref.namelist()
        for file in list:
            if re.search(r"ComicInfo", os.path.basename(file), re.IGNORECASE):
                return True
    return False


def print_end_of_program_stats():
    print("\n\n\n")
    print("Successful ISBN Retrievals: " + str(len(successful_isbn_retrievals)))
    print("Unsuccessful ISBN Retrievals: " + str(len(unsuccessful_isbn_retrievals)))
    print("Successful API Matches: " + str(len(successful_api_matches)))
    print("Unsuccessful API Matches: " + str(len(unsuccessful_api_matches)))
    print("\n\n\n")


# convert array of strings into one common seperated string
def convert_array_to_string(array):
    string = ""
    for item in array:
        string += item + " "
    return string


def clean_epub_writers(writers_from_epub):
    writers = []
    for item in writers_from_epub:
        item = re.sub("[^a-zA-Z]\s", "", item)
        item = item.translate(str.maketrans("", "", string.punctuation))
        item = item.strip()
        # if the item isn't already in writers, append it
        if not item in writers:
            writers.append(item)
    return writers


def convert_writers_object_to_string_array(obj):
    obj_strings = []
    if hasattr(obj, "writer"):
        if obj.writer.name:
            for item in obj.writer.name:
                obj_strings.append(item.strip())
    if hasattr(obj, "penciller"):
        if obj.penciller.name:
            for item in obj.penciller.name:
                obj_strings.append(item.strip())
    if hasattr(obj, "inker"):
        if obj.inker.name:
            for item in obj.inker.name:
                obj_strings.append(item.strip())
    if hasattr(obj, "letterer"):
        if obj.letterer.name:
            for item in obj.letterer.name:
                obj_strings.append(item.strip())
    if hasattr(obj, "cover"):
        if obj.cover.name:
            for item in obj.cover.name:
                obj_strings.append(item.strip())
    if hasattr(obj, "editor"):
        if obj.editor.name:
            for item in obj.editor.name:
                obj_strings.append(item.strip())
    return obj_strings


# Runs various logic to determine whether or not the upgrade will be approved.
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
                            if re.search(writer, item, re.IGNORECASE) or re.search(
                                flipped, item, re.IGNORECASE
                            ):
                                writers_from_api.remove(writer)
                else:
                    if writer and re.search(writer, epub_writers_string, re.IGNORECASE):
                        # remove from epub_writers_string
                        for item in writers_from_api:
                            if re.search(writer, item, re.IGNORECASE):
                                writers_from_api.remove(writer)
        if writers_from_api:
            for item in writers_from_api:
                if item != writers_from_api[-1]:
                    result += item + ", "
                else:
                    result += item
    elif not writers_from_epub and writers_from_api:
        result = writers_from_api
    else:
        print("No writers found in epub or api")
    return result


def check_for_publisher_upgrade(publisher_from_epub, publisher_from_api):
    if publisher_from_epub and publisher_from_api:
        if publisher_from_epub == publisher_from_api:
            return False
        else:
            return True
    elif publisher_from_api and not publisher_from_epub:
        return True
    else:
        return False


def check_for_published_date_upgrade(published_date_from_epub, published_date_from_api):
    if not re.search(r"\d", published_date_from_epub):
        published_date_from_epub = ""
    if published_date_from_epub and published_date_from_api:
        epub_year = published_date_from_epub[0:4]
        if not re.search(r"\d", epub_year):
            epub_year = ""
        api_year = published_date_from_api[0:4]
        if not re.search(r"\d", api_year):
            api_year = ""
        epub_month = published_date_from_epub[5:7]
        if not re.search(r"\d", epub_month):
            epub_month = ""
        api_month = published_date_from_api[5:7]
        if not re.search(r"\d", api_month):
            api_month = ""
        epub_day = published_date_from_epub[8:10]
        if not re.search(r"\d", epub_day):
            epub_day = ""
        api_day = published_date_from_api[8:10]
        if not re.search(r"\d", api_day):
            api_day = ""
        if epub_year == api_year and epub_month == api_month and epub_day == api_day:
            return False
        elif published_date_from_epub != published_date_from_api:
            return True
        elif published_date_from_epub == published_date_from_api:
            return False
    elif published_date_from_api and not published_date_from_epub:
        return True
    else:
        return False
    return False


# Convert comma seperated string to list
def convert_to_list(string):
    if string:
        if "," in string:
            string = string.split(",")
            string = [item.strip() for item in string]
            string = [item for item in string if item]
        else:
            string = [string]
    return string


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


def get_metadata_from_epub_via_calibre(epub_path):
    command = ["ebook-meta", epub_path]
    data = execute_command(command)
    data = data.split("\n")
    data = [x for x in data if x]
    number = ""
    title = ""
    title_sort = ""
    author = ""
    publisher = ""
    series = ""
    languages = ""
    published_date = ""
    identifiers = ""
    isbn = ""
    comments = ""
    part = ""
    average_rating = ""
    series_id = ""
    api_link = ""
    maturity_rating = ""
    genres = []
    tags = []
    for line in data:
        if re.search(r"((Title)\s+:.*)", line, re.IGNORECASE):
            title = re.sub(r"((Title)\s+:)", "", line).strip()
            continue
        if re.search(r"((Title sort)\s+:.*)", line, re.IGNORECASE):
            title_sort = re.sub(r"((Title sort)\s+:)", "", line).strip()
            continue
        if re.search(r"((Author\(s\))\s+:.*)", line, re.IGNORECASE):
            author = re.sub(r"((Author\(s\))\s+:)", "", line).strip()
            continue
        if re.search(r"((Publisher)\s+:.*)", line, re.IGNORECASE):
            publisher = re.sub(r"((Publisher)\s+:)", "", line).strip()
            continue
        if re.search(r"((Series)\s+:.*)", line, re.IGNORECASE):
            series = re.sub(r"((Series)\s+:)", "", line).strip()
            number_search = re.search(r"(#[0-9]+((\.[0-9]+)?)+)", line, re.IGNORECASE)
            if number_search:
                number = number_search.group(0)
                number = re.sub(r"#", "", number).strip()
                number = set_num_as_float_or_int(number)
            series = re.sub(r"(#[0-9]+((\.[0-9]+)?)+)", "", series).strip()
            continue
        if re.search(r"((Languages)\s+:.*)", line, re.IGNORECASE):
            languages = re.sub(r"((Languages)\s+:)", "", line).strip()
            if languages:
                languages = standardize_tag(languages)
            continue
        if re.search(r"((Published)\s+:.*)", line, re.IGNORECASE):
            published_date = re.sub(r"((Published)\s+:)", "", line).strip()
            year = published_date[0:4]
            month = published_date[5:7]
            if month and len(month) == 1:
                month = "0" + month
            day = published_date[8:10]
            if day and len(day) == 1:
                day = "0" + day
            published_date = str(year) + "-" + str(month) + "-" + str(day)
            if re.search(r"(-+$)", published_date):
                published_date = re.sub(r"(-+$)", "", published_date).strip()
            continue
        if re.search(r"((Identifiers)\s+:.*)", line, re.IGNORECASE):
            identifiers = re.sub(r"((Identifiers)\s+:)", "", line).strip()
            if re.search(r"(series_id:.*)", identifiers, re.IGNORECASE):
                series_id = re.search(
                    r"(series_id:.*)", identifiers, re.IGNORECASE
                ).group(0)
                if re.search(r"(series_id:.*,)", series_id, re.IGNORECASE):
                    series_id = re.sub(r",.*", "", series_id).strip()
            isbn = re.search(rf"isbn:{isbn_13_regex}", identifiers, re.IGNORECASE)
            if isbn:
                isbn = isbn.group(0)
                isbn = re.sub(r"[^0-9]", "", isbn)
            else:
                isbn = ""
            continue
        if re.search(r"((Comments)\s+:.*)", line, re.IGNORECASE):
            comments = re.sub(r"((Comments)\s+:)", "", line).strip()
            comments = str(comments)
            comments = comments.replace("\u200b", "")
            continue
        if re.search(r"((Rating)\s+:.*)", line, re.IGNORECASE):
            average_rating = re.sub(r"((Rating)\s+:)", "", line).strip()
            average_rating = set_num_as_float_or_int(average_rating)
            continue
        if re.search(r"((Rating)\s+:.*)", line, re.IGNORECASE):
            average_rating = re.sub(r"((Rating)\s+:)", "", line).strip()
            average_rating = set_num_as_float_or_int(average_rating)
            continue
        # Calibre calls the genres tags
        if re.search(r"((Tags)\s+:.*)", line, re.IGNORECASE):
            genres = re.sub(r"((Tags)\s+:)", "", line).strip()
            genres = convert_to_list(genres)
            genres = sorted(genres)
            continue
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
    )


def clean_below_similarity_score(
    basename, array_list, volume_one_summary, require_summary_match=False
):
    bases = []
    new_results = []
    volume_one_setences = []
    if volume_one_summary:
        volume_one_setences_search = sent_tokenize(volume_one_summary.strip())
        if volume_one_setences_search:
            volume_one_setences = volume_one_setences_search
        else:
            print("No sentences found in: " + volume_one_summary)
    else:
        print("No volume one summary passed in.")
    clean_base = remove_punctuation(basename).strip()
    bases.append(clean_base)
    if translate_titles and not clean_base.isdigit() and not require_summary_match:
        try:
            clean_base_jp = ts.google(clean_base, to_language="ja")
            bases.append(clean_base_jp)
        except:
            print("Failed to translate: " + clean_base)
    # loop through arary_list, and put any item that has item.title.english at the front of the list
    if len(array_list) > 1:
        for item in array_list[:]:
            if hasattr(item, "title"):
                if hasattr(item.title, "english"):
                    if item.title.english:
                        # remove and insert at the front of the list
                        array_list.remove(item)
                        array_list.insert(0, item)
    for item in array_list:
        sentences = []
        if item.description:
            sentences_search = sent_tokenize(item.description.strip())
            if sentences_search:
                sentences = sentences_search
            else:
                print("No sentences found in: " + item.description)
        else:
            print("No description found to split sentences from.")
        comparisions = []
        # remove any item in volume_one_sentences and sentences where length is less than 3
        if volume_one_setences and sentences:
            volume_one_setences = [
                sentence for sentence in volume_one_setences if len(sentence) >= 3
            ]
            sentences = [sentence for sentence in sentences if len(sentence) >= 3]
            # remove any html from the sentences
            sentences = [re.sub(r"<[^>]*>", "", sentence) for sentence in sentences]
            for sentence in volume_one_setences:
                for compare_sentence in sentences:
                    clean_sentence = ""
                    clean_compare_sentence = ""
                    if sentence and compare_sentence:
                        clean_sentence = remove_punctuation(sentence).strip()
                        clean_compare_sentence = remove_punctuation(
                            compare_sentence
                        ).strip()
                        if clean_sentence and clean_compare_sentence:
                            sentences_similarity_score = 0
                            sentences_similarity_score = similar(
                                clean_sentence,
                                clean_compare_sentence,
                            )
                            if sentences_similarity_score >= sentence_similarity_score:
                                send_change_message(
                                    '\n\t\tSentence:\n\t\t"'
                                    + sentence
                                    + '"\n\t\t\tIs similar to:\n\t\t"'
                                    + compare_sentence
                                    + '"\n\t\t\twith a score of '
                                    + str(sentences_similarity_score)
                                )
                                new_results = []
                                new_results.append(item)
                                return new_results
                        else:
                            send_error_message(
                                clean_sentence
                                + " or "
                                + clean_compare_sentence
                                + " empty after removing punctuation."
                            )
        if not require_summary_match:
            if hasattr(item.title, "english"):
                compare_name_english = remove_punctuation(item.title.english).strip()
                if compare_name_english not in comparisions:
                    comparisions.append(compare_name_english)
                if translate_titles and not compare_name_english.isdigit():
                    try:
                        compare_english_translated_japanese = ts.google(
                            compare_name_english, to_language="ja"
                        )
                        if compare_english_translated_japanese not in comparisions:
                            comparisions.append(compare_english_translated_japanese)
                        print(
                            "\t\tTranslated English Title to JP: "
                            + compare_english_translated_japanese
                        )
                    except:
                        print(
                            "\tFailed to translate English Title to JP: "
                            + compare_name_english
                        )
            if hasattr(item.title, "romaji"):
                compare_name_romaji = remove_punctuation(item.title.romaji).strip()
                if compare_name_romaji not in comparisions:
                    comparisions.append(compare_name_romaji)
                if translate_titles and not compare_name_romaji.isdigit():
                    try:
                        compare_translated_romaji = ts.google(
                            compare_name_romaji, to_language="en"
                        )
                        if compare_translated_romaji not in comparisions:
                            comparisions.append(compare_translated_romaji)
                        print("\t\tTranslated Romaji: " + compare_translated_romaji)
                    except Exception as e:
                        send_error_message(e)
                    try:
                        translated_romaji_to_jp = ts.google(
                            compare_name_romaji, to_language="ja"
                        )
                        if translated_romaji_to_jp not in comparisions:
                            comparisions.append(translated_romaji_to_jp)
                        print(
                            "\t\tTranslated Romaji Title to JP: "
                            + translated_romaji_to_jp
                        )
                    except Exception as e:
                        send_error_message(e)
            if hasattr(item.title, "native"):
                compare_name_native = remove_punctuation(item.title.native).strip()
                if compare_name_native not in comparisions:
                    comparisions.append(compare_name_native)
                if (
                    translate_titles
                    and not compare_name_native.isdigit()
                    and not re.search(r"([A-Za-z])", compare_name_native)
                ):
                    try:
                        compare_translated_native = ts.google(
                            compare_name_native, to_language="en"
                        )
                        if compare_translated_native not in comparisions:
                            comparisions.append(compare_translated_native)
                        print("\t\tTranslated Native: " + compare_translated_native)
                    except Exception as e:
                        send_error_message(e)
            if hasattr(item, "synonyms"):
                for synonym in item.synonyms:
                    if synonym not in comparisions:
                        comparisions.append(synonym)
                    if (
                        translate_titles
                        and not synonym.isdigit()
                        and not re.search(r"([A-Za-z])", synonym)
                    ):
                        try:
                            compare_translated_synonym = ts.google(
                                synonym, to_language="en"
                            )
                            if compare_translated_synonym not in comparisions:
                                comparisions.append(compare_translated_synonym)
                        except Exception as e:
                            send_error_message(e)
            for base in bases:
                for comparison in comparisions:
                    similarity_score = 0
                    similarity_score = similar(
                        remove_punctuation(base), remove_punctuation(comparison)
                    )
                    if similarity_score >= required_similarity_score:
                        new_results = []
                        new_results.append(item)
                        return new_results
                    elif similarity_score >= 0.965:
                        new_results.append(item)
    return new_results


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


def filter_by_country(results, country_raws_regex):
    new_results = []
    for i in results:
        if (
            hasattr(i, "country")
            and i.country
            and re.search(
                country_raws_regex,
                i.country,
                re.IGNORECASE,
            )
        ):
            new_results.append(i)
    return new_results


def filter_by_format(results, format_array):
    new_results = []
    for item in results:
        if hasattr(item, "format") and item.format in format_array:
            new_results.append(item)
    return new_results


def filter_out_non_ids(results):
    new_results = []
    for item in results:
        if isinstance(item, list):
            for subitem in item:
                if hasattr(subitem, "id") and subitem.id:
                    new_results.append(subitem)
        else:
            if hasattr(item, "id") and item.id:
                new_results.append(item)
    return new_results


def search_anilist(basename, type_of_dir, cover_file_path, volume_one_summary):
    end_result = None
    try:
        client = anilist.Client()
        send_change_message(
            "-----------------------------------------------------\n"
            + "Searching Anilist For: "
            + basename
            + " "
            + str(type_of_dir)
            + "\n-----------------------------------------------------"
        )
        search = client.search_manga(basename, limit=10)
        shortened_search = ""
        shortened_basename = ""
        shortened_search_results = []
        if re.search(r"(\s(-|\+)\s)", basename):
            shortened_basename = re.sub(r"(\s(-|\+)\s.*)", "", basename).strip()
        if shortened_basename:
            send_change_message(
                "\tShortened Basename: "
                + shortened_basename
                + "\n-----------------------------------------------------"
            )
            shortened_search = client.search_manga(shortened_basename, limit=10)
            shortened_search = filter_out_non_ids(shortened_search)
        shortened_search_results = [client.get_manga(i.id) for i in shortened_search]
        shortened_search_results = filter_by_country(
            shortened_search_results, r"(jpn?|japan|japanese)"
        )
        shortened_search_results = filter_by_format(
            shortened_search_results, type_of_dir
        )
        shortened_search_results = clean_below_similarity_score(
            shortened_basename,
            shortened_search_results,
            volume_one_summary,
            require_summary_match=True,
        )
        if shortened_search_results and len(shortened_search_results) == 1:
            search = shortened_search_results
            send_change_message(
                "\t\tFound result using shortened basename: "
                + str(shortened_search_results[0].title)
            )
        else:
            shortened_search_results = []
        if search and len(search) > 0:
            matches = []
            id_results = []
            id_results_filtered = []
            if not shortened_search_results:
                for s in search:
                    if isinstance(s, list):
                        for item in s:
                            if hasattr(item, "id") and item.id:
                                id = item.id
                                result = client.get_manga(id)
                                id_results.append(result)
                            if hasattr(item, "title"):
                                print("\t" + str(item.title))
            else:
                id_results = shortened_search_results
            for i in id_results:
                if not (
                    hasattr(i, "country")
                    and i.country
                    and re.search(
                        r"(jpn?|japan|japanese)",
                        i.country,
                        re.IGNORECASE,
                    )
                ):
                    print(
                        "\t\t"
                        + str(i.title)
                        + " - "
                        + str(i.url)
                        + " has an invalid country"
                        + " - country: "
                        + str(i.country)
                        + ", removing from results"
                    )
                    id_results.remove(i)
            print("\n\tTotal Search Results: " + str(len(id_results)))
            id_results_filtered = [
                x
                for x in id_results
                if hasattr(x, "format") and type_of_dir and x.format in type_of_dir
            ]
            id_results_filtered = clean_below_similarity_score(
                basename, id_results_filtered, volume_one_summary
            )
            # regex the first word in basename
            first_word_in_base_name = re.search(
                r"\w+", remove_punctuation(basename)
            ).group(0)
            id_results_filtered_first_word = []
            if first_word_in_base_name:
                id_results_filtered_first_word = [
                    x
                    for x in id_results_filtered
                    if hasattr(x, "title")
                    and x.title
                    and (
                        re.search(
                            first_word_in_base_name,
                            remove_punctuation(str(x.title)),
                            re.IGNORECASE,
                        )
                        or re.search(
                            first_word_in_base_name,
                            remove_punctuation(str(x.synonyms)),
                            re.IGNORECASE,
                        )
                    )
                ]
            print(
                "\n\tTotal Filtered Results: "
                + str(len(id_results_filtered_first_word))
                + " ("
                + first_word_in_base_name
                + ")"
            )
            if id_results_filtered_first_word:
                for title in id_results_filtered_first_word[:]:
                    data = title
                    # create anilist result object
                    anilist_result = AnilistResult()
                    # set the anilist result object properties
                    # check if object has attribute
                    if hasattr(data, "country"):
                        if data.country:
                            anilist_result.country = data.country
                        else:
                            anilist_result.country = ""
                    else:
                        anilist_result.country = ""
                    if hasattr(data, "cover"):
                        if data.cover:
                            anilist_result.cover = data.cover
                        else:
                            anilist_result.cover = ""
                    else:
                        anilist_result.cover = ""
                    if hasattr(data, "description"):
                        if data.description:
                            anilist_result.description = data.description
                        else:
                            anilist_result.description = ""
                    else:
                        anilist_result.description = ""
                    if hasattr(data, "description_short"):
                        if data.description_short:
                            anilist_result.description_short = data.description_short
                        else:
                            anilist_result.description_short = ""
                    else:
                        anilist_result.description_short = ""
                    if hasattr(data, "end_date"):
                        if data.end_date:
                            anilist_result.end_date = data.end_date
                        else:
                            anilist_result.end_date = ""
                    else:
                        anilist_result.end_date = ""
                    if hasattr(data, "genres"):
                        if data.genres:
                            anilist_result.genres = list(data.genres)
                            anilist_result.genres.sort()
                        else:
                            anilist_result.genres = []
                    else:
                        anilist_result.genres = []
                    if hasattr(data, "id"):
                        if data.id:
                            anilist_result.id = data.id
                        else:
                            anilist_result.id = ""
                    else:
                        anilist_result.id = ""
                    if hasattr(data, "popularity"):
                        if data.popularity:
                            anilist_result.popularity = data.popularity
                        else:
                            anilist_result.popularity = ""
                    else:
                        anilist_result.popularity = ""
                    if hasattr(data, "score"):
                        if data.score:
                            anilist_result.score = data.score
                        else:
                            anilist_result.score = ""
                    else:
                        anilist_result.score = ""
                    if hasattr(data, "staff"):
                        if data.staff:
                            anilist_result.staff = data.staff
                        else:
                            anilist_result.staff = ""
                    else:
                        anilist_result.staff = ""
                    if hasattr(data, "start_date"):
                        if data.start_date:
                            anilist_result.start_date = data.start_date
                        else:
                            anilist_result.start_date = ""
                    else:
                        anilist_result.start_date = ""
                    if hasattr(data, "status"):
                        if data.status:
                            anilist_result.status = data.status
                        else:
                            anilist_result.status = ""
                    else:
                        anilist_result.status = ""
                    if hasattr(data, "synonyms"):
                        if data.synonyms:
                            anilist_result.synonyms = data.synonyms
                        else:
                            anilist_result.synonyms = ""
                    else:
                        anilist_result.synonyms = ""
                    if hasattr(data, "tags"):
                        if data.tags:
                            anilist_result.tags = list(data.tags)
                            anilist_result.tags.sort()
                        else:
                            anilist_result.tags = []
                    else:
                        anilist_result.tags = []
                    if hasattr(data, "title"):
                        if data.title:
                            anilist_result.title = data.title
                        else:
                            anilist_result.title = ""
                    else:
                        anilist_result.title = ""
                    if hasattr(data, "url"):
                        if data.url:
                            anilist_result.url = data.url
                        else:
                            anilist_result.url = ""
                    else:
                        anilist_result.url = ""
                    if hasattr(data, "volumes"):
                        if data.volumes:
                            anilist_result.volumes = data.volumes
                        else:
                            anilist_result.volumes = ""
                    else:
                        anilist_result.volumes = ""
                    if anilist_result.cover:
                        online_image_link = anilist_result.cover
                        if anilist_result.title:
                            if hasattr(anilist_result.title, "english"):
                                english_similarity = similar(
                                    remove_punctuation(
                                        anilist_result.title.english
                                    ).strip(),
                                    remove_punctuation(basename).strip(),
                                )
                            if hasattr(anilist_result.title, "romaji"):
                                romaji_similarity = similar(
                                    remove_punctuation(
                                        anilist_result.title.romaji
                                    ).strip(),
                                    remove_punctuation(basename).strip(),
                                )
                            if cover_file_path:
                                if os.path.isfile(cover_file_path):
                                    scores = []
                                    images = []
                                    if hasattr(
                                        online_image_link,
                                        "extra_large",
                                    ):
                                        images.append(online_image_link.extra_large)
                                    if hasattr(online_image_link, "large"):
                                        images.append(online_image_link.large)
                                    if hasattr(online_image_link, "medium"):
                                        images.append(online_image_link.medium)
                                    if hasattr(online_image_link, "small"):
                                        images.append(online_image_link.small)
                                    if hasattr(online_image_link, "tiny"):
                                        images.append(online_image_link.tiny)
                                    score = 0
                                    if len(images) == 1:
                                        score = process_image_link_temp_for_anilist(
                                            cover_file_path,
                                            online_image_link,
                                        )[0]
                                    else:
                                        for link in images:
                                            score = process_image_link_temp_for_anilist(
                                                cover_file_path,
                                                link,
                                            )
                                            if score:
                                                scores.append(score[0])
                                        if len(scores) > 0:
                                            score = max(scores)
                                    if not score:
                                        send_error_message(
                                            "Score does not have a value!"
                                        )
                                        continue
                                    if (
                                        score >= required_image_ssim_score
                                        or len(id_results_filtered_first_word) == 1
                                    ):
                                        anilist_result.similarity_score = score
                                        matches.append(anilist_result)
                                else:
                                    send_error_message("\tNo cover file found")
            else:
                send_error_message("\tNo results found")
            # print the match in matches with the highest similarity score
            if len(matches) > 0:
                # order the matches array by the highest similarity score
                matches = sorted(
                    matches,
                    key=lambda x: x.similarity_score,
                    reverse=True,
                )
                matches[0].local_image_path = cover_file_path
                print("\t\t-----------------------------------------------------")
                print("\t\tBest Match For: " + basename)
                print("\t\t-----------------------------------------------------")
                print("\t\tTitle ID: " + str(matches[0].id))
                send_change_message("\t\tTitles: " + str(matches[0].title))
                send_change_message("\t\tGenres: " + str(matches[0].genres))
                send_change_message("\t\tTags: " + str(matches[0].tags))
                send_change_message("\t\tURL: " + str(matches[0].url))
                print("\t\tOnline Image URL: " + matches[0].cover.extra_large)
                print("\t\t-----------------------------------------------------")
                print("\t\tSSIM Score: " + str(matches[0].similarity_score))
                print("\t\t-----------------------------------------------------")
                end_result = matches[0]
            else:
                send_error_message("\t\tBasename: " + basename)
                send_error_message("\t\tNo matches found.")
                # for item in id_results_filtered:
                #     send_error_message("\t\t\t" + str(item.title))
                #     send_error_message("\t\t\t\t" + str(item.url))
        else:
            send_error_message("\tNo search results found.")
    except Exception as e:
        print(e)
    if not end_result:
        write_to_file(
            "no_search_results_from_anilist.txt",
            basename,
            without_date=True,
            check_for_dup=True,
        )
    return end_result


# find file that is named cover in list of files
def find_cover_file(root):
    """
    It takes a root directory as an argument, and returns the path to the cover file if it exists, or an
    empty string if it doesn't

    :param root: the directory to search for the cover file
    :return: The path to the cover file.
    """
    if os.path.isdir(root):
        # pull file list from root directory
        files = os.listdir(root)
        files = remove_hidden_files(files)
        for extension in image_extensions:
            for file in files:
                if file == "cover." + extension:
                    return os.path.join(root, file)
    else:
        send_error_message(
            "\tPassed root directory does not exist when searching for cover file: "
            + root
        )
    return ""


# convert list of strings to a single string seperated by commas
def list_to_string(list):
    """
    It takes a list of strings as an argument, and returns a single string seperated by commas.

    :param list: the list of strings to convert to a single string
    :return: the single string
    """
    return ", ".join(list)


# compare metadata between the api result and the local epub file
def compare_metadata(book, epub_path, files):
    if write_metadata_to_file:
        try:
            extension = get_file_extension(epub_path)
            data = ""
            zip_comments_to_be_written = []
            cbz_changes = []
            data_comparison = []
            anilist_metadata = ""
            cover_file_path = find_cover_file(root)
            if extension == "epub":
                data = get_metadata_from_epub_via_calibre(epub_path)
                vol_one_check = False
                if isinstance(book.volume, list):
                    if 1 in book.volume:
                        vol_one_check = True
                elif book.volume == 1:
                    vol_one_check = True
                if vol_one_check and book.series and cover_file_path:
                    anilist_metadata = search_anilist(
                        book.series, ["NOVEL"], cover_file_path, book.summary
                    )
                    if anilist_metadata:
                        if anilist_metadata.genres:
                            book.genres = anilist_metadata.genres
                        if anilist_metadata.tags:
                            book.tags = anilist_metadata.tags
            elif extension == "cbz":
                # comicinfo = get_file_from_zip(epub_path, "comicinfo.xml")
                # tags = None
                # if comicinfo:
                #     comicinfo = comicinfo.decode("utf-8")
                #     # not parsing pages correctly
                #     comicinfo = parse_comicinfo_xml(comicinfo)
                data = parse_comictagger_output(epub_path)
                vol_one_check = False
                if isinstance(book.volume, list):
                    if 1 in book.volume:
                        vol_one_check = True
                elif book.volume == 1:
                    vol_one_check = True
                if vol_one_check and book.series and cover_file_path:
                    anilist_metadata = search_anilist(
                        book.series,
                        ["MANGA", "ONE_SHOT"],
                        cover_file_path,
                        book.summary,
                    )
                    if anilist_metadata:
                        if anilist_metadata.genres:
                            book.genres = anilist_metadata.genres
                        if anilist_metadata.tags:
                            book.tags = anilist_metadata.tags
            print(
                "--------------------------------Metadata Check----------------------------------"
            )
            # formatting still remains from bookwalker scraper, formatting does not remain when reading in file
            # thus it will infinitely rewrite unless I remove it, this is only a band-aid fix
            if extension == "cbz" and re.search(
                "bookwalker|kobo", book.api_link, re.IGNORECASE
            ):
                book_sum_compare = re.sub(r"(\t|\n|\r)", "", book.summary)
            else:
                book_sum_compare = book.summary
            if convert_to_ascii(book_sum_compare) != convert_to_ascii(data.comments):
                print_diff(data.comments, book.summary)
                if extension == "epub":
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
                if extension == "epub":
                    update_metadata(
                        "ebook-meta",
                        epub_path,
                        str(data.isbn),
                        book.isbn,
                        "ISBN",
                        "--isbn",
                    )
            if book.isbn and extension == "cbz":
                zip_comments_to_be_written.append("isbn:" + str(book.isbn))
            if extension == "cbz":
                author_upgrade_result = check_for_author_upgrade(
                    data.credits, book.writer
                )
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
                                str(
                                    convert_writers_object_to_string_array(data.credits)
                                )
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
                extension == "epub"
                and data.author
                and re.search(r"\band\b", data.author, re.IGNORECASE)
            ):
                seperated = re.sub(
                    r"((\s+)?([\(\{\[])(.*)([\]\}\)])(\s+)?)", "", data.author
                ).strip()
                seperated = re.split(r"(\band\b|&)", seperated, flags=re.IGNORECASE)
                seperated = [
                    x
                    for x in seperated
                    if not re.search(r"\band\b|&", x, re.IGNORECASE)
                ]
                seperated = [
                    re.sub(r"((\s+)?([\(\{\[])(.*)([\]\}\)])(\s+)?)", "", x).strip()
                    for x in seperated
                ]
                seperated = [re.sub(r"[^\w\s]", "", x).strip() for x in seperated]
                formatted = ""
                for item in seperated:
                    if item != seperated[-1]:
                        formatted += item + "&"
                    else:
                        formatted += item
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    data.author,
                    formatted,
                    "Authors",
                    "-a",
                )
            if check_for_published_date_upgrade(
                data.published_date, book.published_date
            ):
                if extension == "epub":
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
                        cbz_changes.append("year=" + str(book.year))
                        data_comparison.append(str(data.year))
                    if book.month != data.month:
                        cbz_changes.append("month=" + str(book.month))
                        data_comparison.append(str(data.month))
                    if book.day != data.day:
                        cbz_changes.append("day=" + str(book.day))
                        data_comparison.append(str(data.day))
            if data.languages != book.language:
                if extension == "epub":
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
            if check_for_publisher_upgrade(data.publisher, book.publisher):
                if extension == "epub":
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
            book_series = remove_punctuation(book.series.lower())
            data_series = remove_punctuation(data.series.lower())
            if book_series != data_series:
                if re.search(r"(([\(\{\[])|([\]\}\)]))", book.series) or re.search(
                    r"(([\(\{\[])|([\]\}\)]))", data.series
                ):
                    print("")
                if extension == "epub":
                    update_metadata(
                        "ebook-meta",
                        epub_path,
                        data.series,
                        book.series,
                        "Series",
                        "--series",
                    )
                else:
                    cbz_changes.append(
                        "series=" + re.sub(r"([,=])", r"^\1", book.series)
                    )
                    data_comparison.append(data.series)
            if data.title != book.title:
                if extension == "epub":
                    update_metadata(
                        "ebook-meta", epub_path, data.title, book.title, "Title", "-t"
                    )
                else:
                    cbz_changes.append("title=" + re.sub(r"([,=])", r"^\1", book.title))
                    data_comparison.append(data.title)
            issue_string = ""
            if book.part:
                if isinstance(book.number, list):
                    book.number = str(book.number[0]) + "." + str(book.part)
                else:
                    book.number = str(book.number) + "." + str(book.part)
                book.number = float(book.number)
            elif isinstance(book.number, list):
                if extension == "epub":
                    book.number = book.number[0]
                elif extension == "cbz":
                    for number in book.number:
                        if number != book.number[-1]:
                            issue_string += str(number) + "-"
                        else:
                            issue_string += str(number)
            book_num_check = book.number
            if isinstance(book.number, list):
                book_num_check = book.number[0]
            else:
                book_num_check = book.number
            if data.number != book_num_check:
                if extension == "epub":
                    update_metadata(
                        "ebook-meta",
                        epub_path,
                        data.number,
                        book.number,
                        "Index Number",
                        "-i",
                    )
                # else:
                #     if not isinstance(book.number, list):
                #         cbz_changes.append("volume=" + str(book.number))
                #     else:
                #         cbz_changes.append("volume=" + str(book.number[0]))
                #     data_comparison.append(data.number)
            if extension == "cbz" and data.issue != book.number:
                if not issue_string:
                    cbz_changes.append("issue=" + str(book.number))
                else:
                    cbz_changes.append("issue=" + issue_string)
                data_comparison.append(data.issue)
            if extension == "epub" and data.average_rating != book.average_rating:
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    data.average_rating,
                    book.average_rating * 2,
                    "Rating",
                    "-r",
                    half=True,
                )
            if data.series_id != book.series_id:
                if extension == "epub":
                    update_metadata(
                        "ebook-meta",
                        epub_path,
                        data.series_id,
                        book.series_id,
                        "Series ID",
                        "--identifier",
                    )
            if book.series_id and extension == "cbz":
                zip_comments_to_be_written.append(book.series_id)
            if anilist_metadata:
                if anilist_metadata.id and extension == "cbz":
                    zip_comments_to_be_written.append(
                        "anilist_id:" + str(anilist_metadata.id)
                    )
                if data.genres != book.genres:
                    if extension == "epub":
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
                    if extension == "epub":
                        print(
                            "\tNo standardized tags tag for epub currently, skipping :'("
                        )
                    else:
                        print(
                            "\tComictagger does not currently support writing the newer anansi tags field, see: https://github.com/comictagger/comictagger/issues/219"
                        )
                        # cbz_changes.append(
                        #     "tags="
                        #     + re.sub(r"([,=])", r"^\1", list_to_string(book.tags))
                        # )
                        # data_comparison.append(list_to_string(data.tags))
            if extension == "cbz":
                if data.api_link != book.api_link:
                    cbz_changes.append(
                        "web_link=" + re.sub(r"([,=])", r"^\1", book.api_link)
                    )
                    data_comparison.append(data.api_link)
                custom_note = re.sub(
                    r"([,=])", r"^\1", "Tagged with manga_isbn_ocr_and_lookup.py"
                )
                if data.notes != custom_note:
                    cbz_changes.append("notes=" + custom_note)
                    data_comparison.append(data.notes)
            if (
                data.maturity_rating != book.maturity_rating
                and book.maturity_rating == "MATURE"
                and data.maturity_rating != "M"
                and extension == "cbz"
            ):
                cbz_changes.append("maturity_rating=M")
                data_comparison.append(data.maturity_rating)
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
                # add string "Identifiers" to the beginning of the list
                combined = "Identifiers: "
                for item in zip_comments_to_be_written:
                    if item != zip_comments_to_be_written[-1]:
                        combined += item + ", "
                    else:
                        combined += item
                if combined and data.zip_comment != str(combined):
                    send_discord_message("Zip Comment: " + combined)
                    print(
                        "\tUpdating Zip Comment: \n"
                        + "\t\tFrom: "
                        + str(data.zip_comment)
                        + " \n\t\tTo: "
                        + str(combined)
                    )
                    if manual_metadata_write_approval:
                        user_input = input("\t\tApprove? (y/n): ")
                        if user_input == "y":
                            result = write_zip_comment(epub_path, combined)
                        elif user_input == "n":
                            print("\tUpdated declined.")
                            return
                    else:
                        result = write_zip_comment(epub_path, combined)
                    if result:
                        print("\tSuccessfully updated.\n")
                    else:
                        send_error_message("\tFailed to update.\n")
        except Exception as e:
            send_error_message(e)
            errors.append(e)
            write_to_file("isbn_script_errors.txt", str(e))
            exc_type, exc_obj, exc_tb = sys.exc_info()
            fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
            print(exc_type, fname, exc_tb.tb_lineno)
    else:
        send_error_message("\tMetadata Write is not enabled")
        send_error_message("\tSkipping Metadata Write")
    print(
        "--------------------------------------------------------------------------------"
    )


def index_in_list(a_list, index):
    print(index < len(a_list))


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
        if not cbz:
            if not skip_print:
                print("\tUpdating " + item + ": ")
                if not half:
                    print(
                        "\t\tFrom: " + str(data_num) + " \n\t\tTo:   " + str(book_num)
                    )
                else:
                    print(
                        "\t\tFrom: "
                        + str(data_num)
                        + " \n\t\tTo:   "
                        + str(book_num / 2)
                    )
            else:
                print("\tUpdating " + item + " to " + str(book_num))
            if item.lower() == "rating" or item.lower() == "index number":
                book_num = str(book_num)
        elif cbz and (len(data_num) == len(book_num)):
            count = len(data_num)
            for num in range(count):
                y_clean = re.sub(r"(\^)([,=])", r"\2", book_num[num])
                y_clean = y_clean.split("=", 1)
                old_value = data_num[num]
                if y_clean[0] != "credit":
                    print("\tUpdating " + y_clean[0].capitalize() + ": ")
                else:
                    print("\tAdding " + y_clean[0].capitalize() + ": ")
                print("\t\tFrom: " + str(old_value) + " \n\t\tTo:   " + str(y_clean[1]))
        else:
            print("\tUpdating " + item + ": ")
            print("\t\tFrom: " + str(data_num) + " \n\t\tTo: " + str(book_num))
        combined = ""
        if cbz:
            for item in book_num:
                if item != book_num[-1]:
                    combined += item + ", "
                else:
                    combined += item
        else:
            combined = book_num
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
        if (
            manual_metadata_write_approval
            and not skip_print
            and epub_path.endswith(".epub")
            or manual_metadata_write_approval
            and epub_path.endswith(".cbz")
        ):
            if input("\tApprove? (y/n): ") == "y":
                execution_result = execute_command(command)
        else:
            execution_result = execute_command(command)
        if (
            execution_result
            and re.search(
                r"changed metadata|Successful match", execution_result, re.IGNORECASE
            )
            and not re.search(
                r"(Warning:|\berror\b|is not a valid tag name)",
                execution_result,
                re.IGNORECASE,
            )
        ):
            print("\tSuccessfully updated\n")
        elif re.search(
            r"(Warning:|\berror\b|is not a valid tag name)",
            execution_result,
            re.IGNORECASE,
        ):
            send_error_message(
                "\t\tWarning found in result, some parts may not have been updated properly."
            )
            send_error_message("\t\tRESULT: " + execution_result)
        else:
            send_error_message("\t\tFailed to update!")
            send_error_message("\n\t\tCommand: " + str(command))
            if epub_path.endswith(".epub"):
                send_error_message(
                    "\t\tDo you have calibre installed? (sudo apt-get install calibre)"
                )
            elif epub_path.endswith(".cbz"):
                send_error_message(
                    "\t\tDo you have comictagger installed? (https://github.com/comictagger/comictagger)"
                )
    except Exception as e:
        send_error_message(e)
        errors.append(e)
        write_to_file("isbn_script_errors.txt", str(e))
        exc_type, exc_obj, exc_tb = sys.exc_info()
        fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
        print(exc_type, fname, exc_tb.tb_lineno)


# Checks for and returns the path of an associated cover file
def find_cover(file_path):
    file_name = os.path.basename(file_path)
    file_name_without_extension = os.path.splitext(file_name)[0]
    directory = os.path.dirname(file_path)
    files = os.listdir(directory)
    files = remove_hidden_files(files)
    # remove any files from files with list comprehension that don't start with file_name_without_extension
    files = [file for file in files if file.startswith(file_name_without_extension)]
    for file in files:
        for extension in image_extensions:
            search = file_name_without_extension + "." + extension
            if file == search:
                return file
    return None


# download an image to ROOT_DIR and return the path
def download_image(url):
    # get image name
    image_name = url.split("/")[-1]
    # if the image already exists, delete it
    image_path = os.path.join(ROOT_DIR, image_name)
    if os.path.isfile(image_path):
        os.remove(image_path)
    # download image as png
    urllib.request.urlretrieve(
        url,
        image_path,
    )
    # return path to image
    return image_path


def PSNR(img1, img2):
    mse = np.mean((img1 - img2) ** 2)
    if mse == 0:
        return 100
    PIXEL_MAX = 255.0
    return 20 * log10(PIXEL_MAX / sqrt(mse)), mse


ssim_scores = []

# compares our two images likness and returns the ssim score
def compare_images(imageA, imageB):
    print("\t\t\t\t\tOnline Size: " + str(imageA.shape))
    print("\t\t\t\t\tCover Size: " + str(imageB.shape))
    grayA = cv2.cvtColor(imageA, cv2.COLOR_BGR2GRAY)
    grayB = cv2.cvtColor(imageB, cv2.COLOR_BGR2GRAY)
    ssim_score = ssim(grayA, grayB)
    ssim_scores.append(ssim_score)
    # resize images to be the same size
    psnr_value = PSNR(imageA, imageB)
    mse_value = psnr_value[1]
    psnr_value = psnr_value[0]
    print("\t\t\t\tSSIM: " + str(ssim_score))
    print("\t\t\t\tPSNR: " + str(psnr_value))
    print("\t\t\t\tMSE: " + str(mse_value))
    return ssim_score, psnr_value, mse_value


def similar(a, b):
    if a == "" or b == "":
        return 0.0
    else:
        return SequenceMatcher(None, a.lower(), b.lower()).ratio()


# Replaces any pesky double spaces
def remove_dual_space(s):
    return re.sub("(\s{2,})", " ", s)


# Removes common words to improve string matching accuracy between a series_name
# from a file name, and a folder name, useful for when releasers sometimes include them,
# and sometimes don't.
def remove_common_words(s):
    if len(s) > 1:
        common_words_to_remove = [
            "the",
            "a",
            "and",
            "&",
            "I",
            "Complete",
            "Series",
            "of",
            "Novel",
            "Light Novel",
            "Manga",
            "Comic",
            "Collection",
            "Edition",
            "((\d+)([-_. ]+)?th)",
            "Anniversary",
            "Deluxe",
            "Omnibus",
            "Digital",
            "Official",
            "Anthology",
            "LN",
            "wa",
            "o",
            "mo",
            "ni",
            "e",
            "de",
            "ga",
            "kara",
            "made",
            "to",
            "ya",
            "no",
            "ne",
            "yo",
        ]
        for word in common_words_to_remove:
            s = re.sub(rf"\b{word}\b", " ", s, flags=re.IGNORECASE).strip()
            s = remove_dual_space(s)
    return s.strip()


# Replaces all numbers
def remove_numbers(s):
    return re.sub("([0-9]+)", "", s, re.IGNORECASE).strip()


# detect language of the passed string using langdetect
def detect_language(s):
    language = ""
    if s:
        try:
            language = detect(s)
        except Exception as e:
            send_error_message(e)
            send_error_message("Attempted language detection on: " + s)
            return language
    return language


# Returns a string without punctuation.
def remove_punctuation(s, space=True):
    s = re.sub(r":", "", s)
    language = ""
    if not s.isdigit():
        language = detect_language(s)
    if space:
        if language and language != "en":
            return remove_dual_space(remove_common_words(re.sub(r"[^\w\s+]", " ", s)))
        else:
            return convert_to_ascii(
                remove_dual_space(remove_common_words(re.sub(r"[^\w\s+]", " ", s)))
            )
    else:
        if language and language != "en":
            return remove_dual_space(remove_common_words(re.sub(r"[^\w\s+]", "", s)))
        else:
            return convert_to_ascii(
                remove_dual_space(remove_common_words(re.sub(r"[^\w\s+]", "", s)))
            )


# convert string to acsii
def convert_to_ascii(s):
    return "".join(i for i in s if ord(i) < 128).strip()


class Person:
    def __init__(self, role, name, primary):
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
        teams,
        genres,
        tags,
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
        self.teams = teams
        self.genres = genres
        self.tags = tags


# dynamically parse all tags from comicinfo.xml and return a dictionary of the tags
def parse_comicinfo_xml(xml_file):
    tags = {}
    if xml_file:
        try:
            tree = ET.fromstring(xml_file)
            for child in tree:
                tags[child.tag] = child.text
        except Exception as e:
            send_error_message(e)
            send_error_message("Attempted to parse comicinfo.xml")
            return tags
    return tags


# use etree and dynamically write all tags to ComicInfo.xml into a cbz file
def write_comicinfo_xml(xml_file, tags):
    if xml_file:
        try:
            root = ET.Element("ComicInfo")
            for tag in tags:
                ET.SubElement(root, tag).text = tags[tag]
            tree = ET.ElementTree(root)
            tree.write(xml_file, encoding="utf-8", xml_declaration=True)
        except Exception as e:
            send_error_message(e)
            send_error_message("Attempted to write comicinfo.xml")
            return False
    return True


# retrieve the file specified from the zip file and return the data for it
def get_file_from_zip(zip_file, file_name):
    result = None
    try:
        with zipfile.ZipFile(zip_file, "r") as z:
            list = z.namelist()
            for file in list:
                if os.path.basename(file).lower() == file_name.lower():
                    result = z.read(file)
                    break
    except Exception as e:
        send_error_message(e)
        send_error_message("Attempted to read file: " + file_name)
    return result


# dynamically parse all html tags and values and return a dictionary of them
def parse_html_tags(html):
    soup = BeautifulSoup(html, "html.parser")
    tags = {}
    for tag in soup.find_all(True):
        tags[tag.name] = tag.get_text()
    return tags


# parse comictagger output
def parse_comictagger_output(path):
    command = [
        "comictagger",
        "-p",
        "-t",
        "cr",
        path,
    ]
    zip_comment = get_zip_comment(path)
    data = execute_command(command)
    data = data.split("\n")
    output = [x for x in data if x]
    isbn = ""
    series_id = ""
    series = ""
    issue = ""
    title = ""
    publisher = ""
    published_date = ""
    year = ""
    month = ""
    day = ""
    volume = ""
    web_link = ""
    scan_info = ""
    characters = ""
    comments = ""
    notes = ""
    credits = []
    credit_obj = ""
    languages = ""
    isbnn = ""
    api_link = ""
    manga = ""
    maturity_rating = ""
    previous_element = ""
    teams = ""
    genres = []
    tags = []
    for line in output:
        if re.search(
            r"((series|issue|title|publisher|year|month|day|volume|language|manga|maturity_rating|web_link|scan_info|characters|comments|notes?|credit|teams|genre|tags):(\s+)?.*)",
            line,
            flags=re.IGNORECASE,
        ):
            # split key and value on :
            key, value = line.split(":", 1)
            # remove any spaces
            key = key.strip()
            value = value.strip()
            if key == "series":
                series = value
                previous_element = "series"
            elif key == "issue":
                if not re.search(r"-", value):
                    issue = set_num_as_float_or_int(value)
                else:
                    issue = [
                        set_num_as_float_or_int(x)
                        for x in convert_list_of_numbers_to_array(value)
                    ]
                previous_element = "issue"
            elif key == "title":
                title = value
                previous_element = "title"
            elif key == "publisher":
                publisher = value
                previous_element = "publisher"
            elif key == "year":
                year = value
                previous_element = "year"
            elif key == "month":
                month = value
                previous_element = "month"
            elif key == "day":
                day = value
                previous_element = "day"
            elif key == "volume":
                if not re.search(r"-", value):
                    volume = set_num_as_float_or_int(value)
                else:
                    volume = [
                        set_num_as_float_or_int(x)
                        for x in convert_list_of_numbers_to_array(value)
                    ]
                previous_element = "volume"
            elif key == "language":
                languages = value
                previous_element = "language"
                if languages:
                    languages = standardize_tag(languages)
            elif key == "web_link":
                api_link = value
                previous_element = "web_link"
            elif key == "scan_info":
                scan_info = value
                previous_element = "scan_info"
            elif key == "characters":
                characters = value.split(",")
                characters = [x.strip() for x in characters]
                previous_element = "characters"
            elif key == "comments":
                comments = value
                previous_element = "comments"
            elif key == "notes" or key == "note":
                notes = value
                previous_element = "notes"
            elif key == "credit":
                credits.append(value)
                previous_element = "credit"
            elif key == "manga":
                manga = value
                previous_element = "manga"
            elif key == "maturity_rating":
                maturity_rating = value
                previous_element = "maturity_rating"
            elif key == "teams":
                teams = value
                previous_element = "teams"
            elif key == "genre":
                genres = value
                genres = convert_to_list(genres)
                genres = sorted(genres)
                previous_element = "genre"
            elif key == "tags":
                tags = value
                tags = convert_to_list(tags)
                tags = sorted(tags)
                previous_element = "tags"
        elif (
            not re.search(r"(^\w+(\s+)?:.*)", line, flags=re.IGNORECASE)
            and previous_element == "comments"
        ):
            comments += " " + line
        elif not re.search(r"ComicRack tags", line, re.IGNORECASE):
            print("\tNo result comcinfo line: " + line)
    if month and len(month) == 1:
        month = "0" + month
    if day and len(day) == 1:
        day = "0" + day
    published_date = str(year) + "-" + str(month) + "-" + str(day)
    if re.search(r"(-+$)", published_date):
        published_date = re.sub(r"(-+$)", "", published_date).strip()
    if credits:
        # remove empty credits
        credits = list(filter(None, credits))
        writer = []
        penciller = []
        inker = []
        letterer = []
        cover = []
        editor = []
        for credit in credits:
            if re.search(
                r"((Writer|Penciller|Inker|Letterer|Cover|Editor):(\s+)?.*)",
                credit,
                re.IGNORECASE,
            ):
                # split key and value on :
                key, value = credit.split(":", 1)
                # remove any spaces
                key = key.strip()
                value = value.strip()
                if key == "Writer":
                    writer.append(value)
                elif key == "Penciller":
                    penciller.append(value)
                elif key == "Inker":
                    inker.append(value)
                elif key == "Letterer":
                    letterer.append(value)
                elif key == "Cover":
                    cover.append(value)
                elif key == "Editor":
                    editor.append(value)
            else:
                send_error_message("\tNo result credit line: " + credit)
        if writer or penciller or inker or letterer or cover or editor:
            credit_obj = Credits(
                Person("Writer", writer, True),
                Person("Penciller", penciller, False),
                Person("Inker", inker, False),
                Person("Letterer", letterer, False),
                Person("Cover", cover, False),
                Person("Editor", editor, False),
            )
    if zip_comment:
        if re.search(r"(series_id:.*)", zip_comment, re.IGNORECASE):
            series_id = re.search(r"(series_id:.*)", zip_comment, re.IGNORECASE).group(
                0
            )
            if re.search(r"(series_id:.*,)", series_id, re.IGNORECASE):
                series_id = re.sub(r",.*", "", series_id).strip()
        isbn = re.search(rf"{isbn_13_regex}", zip_comment, re.IGNORECASE)
        if isbn:
            isbn = isbn.group(0)
            isbn = re.sub(r"[^0-9]", "", isbn)
        else:
            isbn = ""
    if not zip_comment:
        zip_comment = ""
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
        credit_obj,
        languages,
        zip_comment,
        api_link,
        characters,
        manga,
        maturity_rating,
        teams,
        genres,
        tags,
    )


# Result class that is used for our image_comparison results from our
# image comparison function
class Image_Result:
    def __init__(self, book, ssim_score, psnr_score, mse_score, image_link):
        self.book = book
        self.ssim_score = ssim_score
        self.psnr_score = psnr_score
        self.mse_score = mse_score
        self.image_link = image_link


# check if a date is in the future
def is_future_date(day, month, year):
    if day or month or year:
        today = datetime.today()
        if not day:
            day = today.day
        else:
            day = int(day)
        if not month:
            month = today.month
        else:
            month = int(month)
        if not year:
            year = today.year
        else:
            year = int(year)
        if day and month and year:
            try:
                date = datetime(year, month, day)
                if date > today:
                    return True
                else:
                    return False
            except ValueError:
                return False
        else:
            return False
    else:
        return False


def clean_api_results(
    results,
    vol_num,
    first_word,
    multi_volume,
    series,
    extension,
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
    if results:
        if not isinstance(results, list):
            results = [results]
        new_results = []
        print("\nFiltering Results " + "[" + str(len(results)) + "]")
        for result in results:
            print(
                "\tResult: "
                + str(results.index(result) + 1)
                + " of "
                + str(len(results))
                + ": ["
                + str(result.title)
                + " - "
                + str(result.series)
                + "]"
                + " - "
                + str(result.isbn)
                + " "
                + str(result.categories)
            )
            passed = True
            if not skip_vol_nums_equal:
                title_vol_num = remove_everything_but_volume_num([result.title])
                try:
                    if (title_vol_num == vol_num or result.volume == vol_num) or (
                        title_vol_num == int(vol_num) or result.volume == int(vol_num)
                    ):
                        print("\t\tPassed volume num check")
                    else:
                        passed = False
                        print("\t\tFailed volume num check")
                except Exception as e:
                    send_error_message(e)
                    errors.append(e)
                    write_to_file("isbn_script_errors.txt", str(e))
                    exc_type, exc_obj, exc_tb = sys.exc_info()
                    fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
                    print(exc_type, fname, exc_tb.tb_lineno)
                    return None
            if not skip_contains_first_word:
                series_no_puct_no_space = remove_punctuation(result.series, space=False)
                series_no_puct_space = remove_punctuation(result.series)
                if re.search(
                    first_word, series_no_puct_no_space, re.IGNORECASE
                ) or re.search(first_word, series_no_puct_space, re.IGNORECASE):
                    print("\t\tPassed first word check")
                else:
                    passed = False
                    print(
                        "\t\tFailed first word check "
                        + "\n\t\t\tFirst Word: "
                        + first_word
                        + "\n\t\t\tSeries: "
                        + result.series
                    )
            if not skip_omnibus_check:
                if multi_volume and (
                    re.search(
                        r"omnibus|omni-bus",
                        result.series,
                        re.IGNORECASE,
                    )
                    or re.search(
                        r"omnibus|omni-bus",
                        result.title,
                        re.IGNORECASE,
                    )
                    or (
                        check_for_multi_volume_file(result.series)
                        or check_for_multi_volume_file(result.title)
                    )
                ):
                    print("\t\tPassed omnibus check")
                elif not multi_volume and not (
                    re.search(
                        r"omnibus|omni-bus",
                        result.series,
                        re.IGNORECASE,
                    )
                    or re.search(
                        r"omnibus|omni-bus",
                        result.title,
                        re.IGNORECASE,
                    )
                ):
                    print("\t\tPassed omnibus check")
                else:
                    passed = False
                    print(
                        "\t\tFailed omnibus check"
                        + "\n\t\t\tSeries: "
                        + result.series
                        + "\n\t\t\tTitle: "
                        + result.title
                    )
            if not skip_manga_keyword_check:
                if extension == "epub" and not (
                    re.search(
                        r"manga",
                        result.title,
                        re.IGNORECASE,
                    )
                    or re.search(
                        r"manga",
                        result.series,
                        re.IGNORECASE,
                    )
                ):
                    print("\t\tPassed manga keyword check")
                elif extension == "cbz" and not (
                    re.search(
                        r"light novel",
                        result.title,
                        re.IGNORECASE,
                    )
                    or re.search(
                        r"light novel",
                        result.series,
                        re.IGNORECASE,
                    )
                ):
                    print("\t\tPassed light novel keyword check")
                else:
                    passed = False
                    print(
                        "\t\tFailed manga/light novel keyword check"
                        + "\n\t\t\tTitle: "
                        + result.title
                        + "\n\t\t\tSeries: "
                        + result.series
                    )
            if not skip_series_similarity:
                score = similar(
                    remove_punctuation(series),
                    remove_punctuation(
                        re.sub(
                            r"\(.*\)",
                            "",
                            result.series,
                        )
                    ),
                )
                if score >= series_similarity_score:
                    print("\t\tPassed series similarity check")
                else:
                    passed = False
                    print(
                        "\t\tFailed series similarity check"
                        + "\n\t\t\tScore: "
                        + str(score)
                        + "\n\t\t\tResult Series: "
                        + result.series
                        + "\n\t\t\tSeries: "
                        + series
                    )
            if not skip_isebook_check:
                todays_year = datetime.now().year
                todays_month = datetime.now().month
                todays_day = datetime.now().day
                if result.is_ebook:
                    print("\t\tPassed is_ebook check")
                elif (
                    square_enix_bypass
                    and re.search(r"Square", result.publisher, re.IGNORECASE)
                    and re.search(r"Enix", result.publisher, re.IGNORECASE)
                ):
                    print(
                        "\t\tis_ebook=False \n\t\t\tpublisher is square-enix, exception made, using paperback metadata."
                    )
                elif (
                    todays_year
                    and todays_month
                    and todays_day
                    and result.year
                    and result.month
                    and result.day
                ) and (
                    is_future_date(int(result.day), int(result.month), int(result.year))
                ):
                    print(
                        "\t\tis_ebook=False, but release date is in the future, assuming digital version, is_ebook check bypassed."
                    )
                else:
                    passed = False
                    print("\t\tFailed is_ebook check")
            if not skip_categories_check:
                if hasattr(result, "categories") and len(result.categories) > 0:
                    if extension == "epub" and re.search(
                        r"Fiction|Novel|Light Novel",
                        result.categories[0],
                        re.IGNORECASE,
                    ):
                        print("\t\tPassed fiction category check")
                    elif extension == "cbz" and re.search(
                        r"Comic|Graphic|Manga", result.categories[0], re.IGNORECASE
                    ):
                        print("\t\tPassed comic/graphic category check")
                    else:
                        if extension == "epub":
                            print("\t\tFailed fiction category check")
                            passed = False
                        elif extension == "cbz":
                            print("\t\tFailed comic/graphic category check")
                            passed = False
                else:
                    print("\t\tFailed Categories check, no categories field present.")
                    passed = False
            if not skip_summary_check:
                if hasattr(result, "summary") and len(result.summary) > 0:
                    if not re.search(
                        r"(Chapter([-_. ]+)?Titles.*)", result.summary, re.IGNORECASE
                    ):
                        print("\t\tPassed summary check")
                    else:
                        passed = False
                        print("\t\tFailed summary check")
                        print("\t\t\tContains chapter titles.")
                        print(result.summary)
                else:
                    print("\t\tFailed summary check")
                    print("\t\t\tNo summary field present or empty summary.")
                    passed = False
            if not skip_language_check:
                if hasattr(result, "language"):
                    if result.language == "en" or result.language == "eng":
                        print("\t\tPassed language check")
                    else:
                        passed = False
                        print("\t\tFailed language check")
                        print("\t\t\tLanguage: " + result.language)
                elif hasattr(result, "summary"):
                    detected_language = detect_language(result.summary)
                    if detected_language == "en":
                        print("\t\tPassed language check")
                    else:
                        passed = False
                        print("\t\tFailed language check")
                        print(
                            "\t\t\tDetected Language on Summary: " + detected_language
                        )
                else:
                    print("\t\tFailed language check")
                    print("\t\t\tNo language field present.")
                    passed = False
            if passed:
                print("\t\t-----Passed all checks-----")
                new_results.append(result)
        return new_results


# Retrieves and returns the volume part from the file name
def get_volume_part(file):
    result = ""
    file = re.sub(
        r".*(LN|Light Novels?|Novels?|Books?|Volumes?|Vols?|V|第|Discs?)([-_. ]|)([-_. ]|)([0-9]+)(\b|\s)",
        "",
        file,
        flags=re.IGNORECASE,
    ).strip()
    search = re.search(r"(\b(Part)([-_. ]|)([0-9]+)\b)", file, re.IGNORECASE)
    if search:
        result = search.group(1)
        result = re.sub(r"(\b(Part)([-_. ]|)\b)", "", result, flags=re.IGNORECASE)
        try:
            return float(result)
        except ValueError as ve:
            send_error_message("Not a float: " + file)
            write_to_file("isbn_script_errors.txt", str(ve))
            result = ""
    return result


def get_search_keyword(s):
    s = remove_common_words(s)
    word_list = s.split()
    number_of_words = len(word_list)
    if number_of_words >= 2:
        return word_list[1]
    else:
        return word_list[0]


# DELETE AFTER RECODING OTHER PROCESS IMAGE LINK METHOD
def process_image_link_temp_for_anilist(cover_path, link):
    try:
        # read the images
        cover_image = cv2.imread(cover_path)
        # download online image
        online_image = requests.get(link).content
        online_image = Image.open(io.BytesIO(online_image))
        online_image = np.array(online_image)
        # online_image = cv2.cvtColor(online_image, cv2.COLOR_BGR2RGB)
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
        send_error_message(e)
        return None


def process_image_link(result, cover_path, link, internal_cover_data):
    cover_image = None
    if internal_cover_data:
        cover_image = Image.open(io.BytesIO(internal_cover_data))
        cover_image = np.array(cover_image)
    elif cover_path:
        cover_image = cv2.imread(cover_path)
    online_image = ""
    print(
        "\t\t\tImage Link "
        + str(result.image_links.index(link) + 1)
        + " of "
        + str(len(result.image_links))
    )
    print("\t\t\t\tImage Link: " + link)
    try:
        online_image_data = requests.get(
            link, headers={"User-Agent": "Mozilla/5.0"}, timeout=5
        )
    except Exception as e:
        print(e)
        return None
    online_image = Image.open(io.BytesIO(online_image_data.content))
    online_image = np.array(online_image)
    online_image = cv2.cvtColor(online_image, cv2.COLOR_BGR2RGB)
    # if cover_image.shape != online_image.shape:
    #     # cover_image = cv2.resize(
    #     #     cover_image, (online_image.shape[1], online_image.shape[0])
    #     # )
    #     online_image = cv2.resize(
    #         online_image, (cover_image.shape[1], cover_image.shape[0])
    #     )
    # resize the two images to the smaller of the two
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
    score = compare_images(online_image, cover_image)
    return Image_Result(
        result,
        score[0],
        score[1],
        score[2],
        link,
    )


# our session object, helps speed things up
# when scraping
session_object = None


def scrape_url(url, strainer=None, headers=None, cookies=None, proxy=None):
    try:
        global session_object
        if not session_object:
            session_object = requests.Session()
        page_obj = None
        if headers and cookies and proxy:
            page_obj = session_object.get(
                url,
                headers=headers,
                cookies=cookies,
                proxies=proxy,
                timeout=10,
            )
        elif headers and cookies:
            page_obj = session_object.get(
                url, headers=headers, cookies=cookies, timeout=10
            )
        elif headers and proxy:
            page_obj = session_object.get(
                url, headers=headers, proxies=proxy, timeout=10
            )
        elif headers:
            page_obj = session_object.get(url, headers=headers, timeout=10)
        elif cookies and proxy:
            page_obj = session_object.get(
                url, cookies=cookies, proxies=proxy, timeout=10
            )
        elif cookies:
            page_obj = session_object.get(url, cookies=cookies, timeout=10)
        elif proxy:
            page_obj = session_object.get(url, proxies=proxy, timeout=10)
        else:
            page_obj = session_object.get(url, timeout=10)
        if page_obj and page_obj.status_code == 403:
            print("\nTOO MANY REQUESTS, WE'RE BEING RATE-LIMTIED!")
        soup = None
        if strainer and page_obj:
            soup = BeautifulSoup(page_obj.text, "lxml", parse_only=strainer)
        else:
            soup = BeautifulSoup(page_obj.text, "lxml")
        return soup
    except Exception as e:
        print("Error: " + str(e))
        return ""


# Retrieves the ids from the soup passed, and returns them.
def get_series_ids(soup, sort=False):
    ids = []
    if soup:
        hrefs = soup.find_all("a", href=True)
        if hrefs:
            # only keep hrefs that contain "/store/books/details"
            filtered_hrefs = [
                href
                for href in hrefs
                if re.search(r"/store/books/details", href["href"])
            ]
            cleaned_hrefs = []
            for item in filtered_hrefs:
                href = item["href"]
                number = item["href"].split("?")[0].rsplit("_", 1)[1]
                number = re.sub(r"[^0-9]", "", number)
                id = re.search(r"id=.*", href).group(0).split("=")[1]
                if re.search(r"(\d+)", number):
                    if float(number) < 10 and len(number) == 1:
                        number = "00" + number
                    elif (
                        float(number) < 100 and float(number) >= 10 and len(number) == 2
                    ):
                        number = "0" + number
                cleaned_hrefs.append({"href": href, "number": number, "id": id})
            # sort by number
            if sort:
                cleaned_hrefs = sorted(cleaned_hrefs, key=lambda k: k["number"])
            if cleaned_hrefs:
                for item in cleaned_hrefs:
                    if item["id"] not in ids:
                        ids.append(item["id"])
                    else:
                        # print("\tduplicate id found: " + str(item["id"]))
                        pass
            else:
                print("\tNo cleaned hrefs")
        else:
            print("\tNo hrefs found")
    else:
        print("\tsoup is None")
    return ids


# Gets the user a webdriver object based on the url passed in
def get_page_driver(url, options=None):
    if options:
        options_driver = webdriver.ChromeOptions()
        for option in options:
            options_driver.add_argument(option)
        driver = webdriver.Chrome(
            service=Service(ChromeDriverManager().install()), options=options_driver
        )
    else:
        driver = webdriver.Chrome(service=Service(ChromeDriverManager().install()))
    driver.get(url)
    return driver


# Takes a google series_id and scrapes all volume ids from the series
# page on google, then returns all those ids with the url portion added
# to the beginning.
def scrape_series_ids(id, sort=False):
    url = "https://play.google.com/store/books/series?id=" + id
    search_results = []
    driver = get_page_driver(
        url,
        [
            "--disable-blink-features=AutomationControlled",
            "window-size=1920,1080",
            "--headless",
            "--disable-gpu",
            "--no-sandbox",
            "--disable-dev-shm-usage",
        ],
    )
    # find all buttons on page with an attribute of aria-label that equals "Scroll Next"
    buttons = driver.find_elements(By.XPATH, '//button[@aria-label="Scroll Next"]')
    if buttons:
        if len(buttons) > 1:
            forward_volumes = buttons[1]
        else:
            forward_volumes = buttons[0]
        # click forward using jsaction until the html doesn't change anymore
        while True:
            html = driver.page_source
            # click forward by using jsaction
            try:
                driver.execute_script("arguments[0].click();", forward_volumes)
                # update source
                time.sleep(1)
            except Exception as e:
                break
            else:
                # find all the hrefs on the page
                soup = BeautifulSoup(driver.page_source, "lxml")
                if sort:
                    ids = get_series_ids(soup, sort=True)
                else:
                    ids = get_series_ids(soup)
                if ids:
                    for id in ids:
                        if id not in search_results:
                            search_results.append(id)
                else:
                    print("\tNo ids found")
    else:
        print("\t\t\tNo buttons, still attempting to scrape ids without clicking.")
        soup = BeautifulSoup(driver.page_source, "lxml")
        if sort:
            ids = get_series_ids(soup, sort=True)
        else:
            ids = get_series_ids(soup)
        if ids:
            for id in ids:
                if id not in search_results:
                    search_results.append(id)
        else:
            print("\tNo ids found")
    return search_results


# gets the user passed result from an epub file
def get_meta_from_file(file, search_regex, extension):
    result = None
    if extension == "epub":
        with zipfile.ZipFile(file, "r") as zf:
            for name in zf.namelist():
                if name.endswith(".opf"):
                    opf_file = zf.open(name)
                    opf_file_contents = opf_file.read()
                    lines = opf_file_contents.decode("utf-8")
                    search = re.search(search_regex, lines, re.IGNORECASE)
                    if search:
                        result = search.group(0)
                        if not re.search(r"subject", search_regex, re.IGNORECASE):
                            result = re.sub(r"<\/?.*>", "", result)
                        result = re.sub(
                            r"(series_id:NONE)", "", result, flags=re.IGNORECASE
                        )
                        if re.search(r"(series_id:.*,)", result, re.IGNORECASE):
                            result = re.sub(r",.*", "", result).strip()
                        break
    elif extension == "cbz":
        zip_comment = get_zip_comment(file)
        if zip_comment:
            search = re.search(search_regex, zip_comment, re.IGNORECASE)
            if search:
                result = search.group(0)
                result = re.sub(r"(series_id:NONE)", "", result, flags=re.IGNORECASE)
                search_two = re.search(search_regex, result, re.IGNORECASE)
                if search_two:
                    result = search_two.group(0)
                else:
                    result = ""
                if re.search(r"(series_id:.*,)", result, re.IGNORECASE):
                    result = re.sub(r",.*", "", result).strip()
    return result


# Removes bracket info from the end of a string.
def remove_bracketed_info_from_name(name):
    return re.sub(r"([\{\[\(][^\)\]\}]*[\)\]\}])", "", name).strip()


# convert string date to xxxx-xx-xx format
# EX: March 16, 2021 -> 2021-03-16
def convert_date_to_yyyy_mm_dd(date):
    if date:
        date = date.strip()
        year = date.split(",")[1].strip()
        month = date.split(" ")[0].strip()
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
            month = str(list(calendar.month_name).index(month))
            if len(month) == 1:
                month = "0" + month
        day = date.split(",")[0].strip()
        if day:
            day = day.split(" ")[1].strip()
            if len(day) == 1:
                day = "0" + day
        if year and month and day:
            yield {
                "date": year + "-" + month + "-" + day,
                "year": year,
                "month": month,
                "day": day,
            }
    else:
        return None


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
            website_url = website_url + "/us/en/search?query=" + str(isbn)
        else:
            print("\t" + website_url)
        kobo_isbn_soup = scrape_url(
            website_url,
            SoupStrainer("div", {"class": "inner-wrap content-main"}),
            {
                "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/86.0.4240.111 Safari/537.36",
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.9",
                "Accept-Encoding": "gzip, deflate, br",
                "Accept-Language": "en-US,en;q=0.9,ja-JP;q=0.8,ja;q=0.7",
                "Cache-Control": "max-age=0",
                "Connection": "keep-alive",
                "Host": "www.kobo.com",
                "Sec-Fetch-Dest": "document",
                "Sec-Fetch-Mode": "navigate",
                "Sec-Fetch-Site": "none",
                "Sec-Fetch-User": "?1",
                "Upgrade-Insecure-Requests": "1",
            },
        )
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
                    series_name = remove_bracketed_info_from_name(series_name)
                    if not volume_number:
                        volume_search = re.search(
                            r"([0-9]+(\.?[0-9]+)?([-_][0-9]+\.?[0-9]+)?)$",
                            series_name,
                        )
                        if volume_search:
                            volume_number = volume_search.group(1)
                            if re.search(r"-", volume_number):
                                volume_number = convert_list_of_numbers_to_array(
                                    volume_number
                                )
                            else:
                                volume_number = set_num_as_float_or_int(volume_number)
                        elif (
                            not contains_volume_keywords(series_name)
                            and not contains_chapter_keywords(series_name)
                            and not re.search(r"([0-9]+)", series_name)
                        ):
                            volume_number = 1
                    if not part:
                        part_search = get_volume_part(series_name)
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
                            series_link = "https://www.kobo.com" + series_link
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
                                summary += p.text.strip() + "\n"
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
                                    summary += li.text.strip() + "\n"
                            else:
                                synopsis_description = lists[0]
                                summary = synopsis_description.text.strip()
                    if summary:
                        title_search_in_summary = get_title_from_description(summary)
                        if title_search_in_summary:
                            title = titlecase(title_search_in_summary)
                        elif volume_number and part:
                            title = (
                                "Volume " + str(volume_number) + " Part " + str(part)
                            )
                        elif volume_number and not part:
                            title = "Volume " + str(volume_number)
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
                                image_link = "https:" + image_link
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
                    #             if category != categories[-1]:
                    #                 category_combined_string += category + ", "
                    #             else:
                    #                 category_combined_string += category
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
                        rating = float(rating)
                        if rating == 0:
                            rating = ""
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
                                    "publishers.txt", publisher, without_date=True
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
                                            month = "0" + month
                                    day = published_date.split(",")[0].strip()
                                    if day:
                                        day = day.split(" ")[1].strip()
                                        if len(day) == 1:
                                            day = "0" + day
                                    if year and month and day:
                                        published_date = year + "-" + month + "-" + day
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
            print("\t\tNo result found using " + website_url)
            return None
        if isbn == 0:
            isbn = ""
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
            "series_id:NONE",
            rating,
            True,
            website_url,
            "",
            "FOR_SALE",
        )
        return book
    except Exception as e:
        send_error_message("Error: " + str(e))
        return None
    return None


def text_search_kobo(query):
    # html format the query with urllib.request
    query = urllib.parse.quote(query)
    soup = scrape_url(
        "https://www.kobo.com/us/en/search?query=" + query,
        SoupStrainer("ul", {"class": "result-items"}),
        {
            "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/86.0.4240.111 Safari/537.36",
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.9",
            "Accept-Encoding": "gzip, deflate, br",
            "Accept-Language": "en-US,en;q=0.9,ja-JP;q=0.8,ja;q=0.7",
            "Cache-Control": "max-age=0",
            "Connection": "keep-alive",
            "Host": "www.kobo.com",
            "Sec-Fetch-Dest": "document",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Site": "none",
            "Sec-Fetch-User": "?1",
            "Upgrade-Insecure-Requests": "1",
        },
    )
    results = []
    if soup:
        # find all li items in the result_items
        li_items = soup.find_all("li")
        if li_items:
            for li in li_items:
                # find <a class="item-link-underlay"
                a_item = li.find("a", {"class": "item-link-underlay"})
                if a_item:
                    # get href from the a_item
                    href = a_item.get("href")
                    if href:
                        results.append("https://www.kobo.com" + href)
                    else:
                        print("No href found for a_item")
                else:
                    print("No a_item found")
        else:
            print("No results found for: " + query)
    return results


# Does a text search on bookwalker, allows filtering by manga or light novels.
# Also allows limiting how many results you want returned.
def text_search_bookwalker(query, category=None, limit=None):
    base_url = "https://global.bookwalker.jp/search/?word="
    query = urllib.parse.quote(query)
    search_url = base_url + query
    if category and category.lower() == "l":
        search_url += "&qcat=3"
    elif category and category.lower() == "m":
        search_url += "&qcat=2"
    print("\tSearch URL: " + search_url)
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
            print("\t\t - No results found for: " + query)
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

        print("\t\t" + link)
        soup = scrape_url(
            link,
            SoupStrainer("div", {"class": "wrap clearfix"}),
            {
                "user-agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/86.0.4240.111 Safari/537.36",
            },
        )
        if soup:
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
            if title and not volume_number:
                volume_search = re.search(
                    r"([0-9]+(\.?[0-9]+)?([-_][0-9]+\.?[0-9]+)?)$",
                    title,
                )
                if volume_search:
                    volume_number = volume_search.group(1)
                    if re.search(r"-", volume_number):
                        volume_number = convert_list_of_numbers_to_array(volume_number)
                    else:
                        volume_number = set_num_as_float_or_int(volume_number)
                elif (
                    not contains_volume_keywords(title)
                    and not contains_chapter_keywords(title)
                    and not re.search(r"([0-9]+)", title)
                ):
                    volume_number = 1
            if not part:
                part_search = get_volume_part(title)
                if part_search:
                    part = part_search
            if title and not volume_number and not part:
                title = ""
            # finding image_link
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
                                    summary += p_item.text.strip() + "\n"
                    else:
                        summary = p_items[0].text.strip()
                else:
                    print("\t\t\t - No summary found")
            else:
                print("\t\t\t - No div_itemprop_description found")
            if summary:
                # use langdetect to detect language of summary and set language with a two letter code
                try:
                    detected_lang = detect(summary)
                    if detected_lang:
                        language = detected_lang
                    else:
                        print("\t\t\t - Language detection failed")
                        print("\t\t\t - No language found")
                except Exception as e:
                    print("\t\t\t - Language detection failed: " + str(e))
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
                elif volume_number and part:
                    if isinstance(volume_number, list):
                        title = (
                            volume_keyword
                            + str(convert_array_to_string_with_dashes(volume_number))
                            + " Part "
                            + str(part)
                        )
                    else:
                        title = (
                            volume_keyword + str(volume_number) + " Part " + str(part)
                        )
                elif volume_number and not part:
                    if isinstance(volume_number, list):
                        title = volume_keyword + str(
                            convert_array_to_string_with_dashes(volume_number)
                        )
                    else:
                        title = volume_keyword + str(volume_number)
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
                                                series_name = (
                                                    remove_bracketed_info_from_name(
                                                        series_name
                                                    )
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
                                                converted_date = list(converted_date)[0]
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
        print("Error: " + str(e))
        return None
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
        "series_id:NONE",
        rating,
        True,
        series_link,
        maturity_rating,
        "FOR_SALE",
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
        print("\t" + link)
        soup = ""
        if not skip:
            soup = scrape_url(
                link,
                SoupStrainer("div", {"id": "pdp-page-container"}),
                {
                    "user-agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/86.0.4240.111 Safari/537.36",
                },
            )
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
                            part_search = get_volume_part(title)
                            if part_search:
                                part = part_search
                                part = set_num_as_float_or_int(part)
                    else:
                        print("\t\t - No title found!")
                    if title and not volume_number:
                        volume_search = re.search(
                            r"([0-9]+(\.?[0-9]+)?([-_][0-9]+\.?[0-9]+)?)$",
                            title,
                        )
                        if volume_search:
                            volume_number = volume_search.group(1)
                            if re.search(r"-", volume_number):
                                volume_number = convert_list_of_numbers_to_array(
                                    volume_number
                                )
                            else:
                                volume_number = set_num_as_float_or_int(volume_number)
                        elif (
                            not contains_volume_keywords(title)
                            and not contains_chapter_keywords(title)
                            and not re.search(r"([0-9]+)", title)
                        ):
                            volume_number = 1
                    if not part:
                        part_search = get_volume_part(title)
                        if part_search:
                            part = part_search
                    if title and not volume_number and not part:
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
                                    titlecase(
                                        remove_bracketed_info_from_name(
                                            contributor_name
                                        )
                                    )
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
                            summary += content_text + " "
                summary = summary.strip()
                # detect langauge of summary
                if summary:
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
                elif volume_number and part:
                    if isinstance(volume_number, list):
                        title = (
                            volume_keyword
                            + str(convert_array_to_string_with_dashes(volume_number))
                            + " Part "
                            + str(part)
                        )
                    else:
                        title = (
                            volume_keyword + str(volume_number) + " Part " + str(part)
                        )
                elif volume_number and not part:
                    if isinstance(volume_number, list):
                        title = volume_keyword + str(
                            convert_array_to_string_with_dashes(volume_number)
                        )
                    else:
                        title = volume_keyword + str(volume_number)
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
                                        series_name = remove_bracketed_info_from_name(
                                            series_name
                                        )
                                        if not part:
                                            part_search = get_volume_part(series_name)
                                            if part_search:
                                                part = part_search
                                                part = set_num_as_float_or_int(part)
                                    if not volume_number:
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
                                            if volume_number == 0:
                                                volume_number = ""
                                else:
                                    if not series_name:
                                        series_name = td_item
                                    if not volume_number:
                                        volume_number = ""
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
        send_error_message(e)
        return None
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
        "series_id:NONE",
        "",
        is_ebook,
        link,
        "",
        for_sale,
    )
    return book


def text_search_barnes_and_noble(query):
    base_url = "https://www.barnesandnoble.com/s/"
    query = urllib.parse.quote(query)
    search_url = base_url + query
    search_url += "/_/N-8qa"
    soup = scrape_url(
        search_url,
        SoupStrainer("div", {"class": "product-shelf-grid plp-grid-qa"}),
        {
            "user-agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/86.0.4240.111 Safari/537.36",
        },
    )
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
                        link = "https://www.barnesandnoble.com" + href
                        if link not in clean_results:
                            clean_results.append(link)
                    else:
                        print("No link found for: " + str(title))
                else:
                    print("No title found for: " + str(result))
        else:
            print("\n\tSleeping for " + str(web_scrape_sleep_time) + " seconds...\n")
            time.sleep(web_scrape_sleep_time)
            second_soup = scrape_url(
                search_url,
                SoupStrainer("div", {"id": "pdp-page-container"}),
                {
                    "user-agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/86.0.4240.111 Safari/537.36",
                },
            )
            if second_soup and second_soup.contents:
                # get full_url from second_soup
                return get_barnes_and_noble_books_meta(
                    search_url, skip=True, data=second_soup
                )
            print("No results found for: " + query)
    else:
        print("No soup found!")
    return clean_results


def search_comic_vine(query, api_key, limit=None):
    books = []
    try:
        session = Comicvine(api_key=api_key, cache=SQLiteCache())
        results = session.search(
            resource=ComicvineResource.ISSUE, query=query, max_results=30
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
                    series_id = "series_id:NONE"
                    store_availability_status = "FOR_SALE"
                    genres = []
                    tags = []
                    if hasattr(result, "site_url"):
                        preview_link = result.site_url
                        if preview_link:
                            print("\tLink: " + preview_link)
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
                        if hasattr(result.image, "original"):
                            image_link = result.image.original
                        else:
                            print("\t\t\t - No original image inside of image_url")
                    else:
                        print("\t\t\t - No image")
                    if hasattr(result, "issue_id"):
                        issue_id = result.issue_id
                        if issue_id:
                            print("\t\tIssue ID: " + str(issue_id))
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
                                volume_number = convert_list_of_numbers_to_array(
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
                            published_date = (
                                str(year) + "-" + str(month) + "-" + str(day)
                            )
                            if re.search(r"(-+$)", published_date):
                                published_date = re.sub(
                                    r"(-+$)", "", published_date
                                ).strip()
                        else:
                            published_date = ""
                    else:
                        print("\t\t\t - No store_date")
                    if name and not volume_number:
                        volume_search = re.search(
                            r"([0-9]+(\.?[0-9]+)?([-_][0-9]+\.?[0-9]+)?)$",
                            name,
                        )
                        if volume_search:
                            volume_number = volume_search.group(1)
                            if re.search(r"-", volume_number):
                                volume_number = convert_list_of_numbers_to_array(
                                    volume_number
                                )
                            else:
                                volume_number = set_num_as_float_or_int(volume_number)
                        elif (
                            not contains_volume_keywords(name)
                            and not contains_chapter_keywords(name)
                            and not re.search(r"([0-9]+)", name)
                        ):
                            volume_number = 1
                    if not part and name:
                        part_search = get_volume_part(name)
                        if part_search:
                            part = part_search
                    if name and not volume_number and not part:
                        name = ""
                    extracted_title = ""
                    if summary:
                        extracted_title = get_title_from_description(summary)
                    volume_keyword = ""
                    if isinstance(volume_number, list):
                        volume_keyword = "Volumes "
                    else:
                        volume_keyword = "Volume "
                    if extracted_title:
                        title = titlecase(extracted_title.strip())
                    elif volume_number and part:
                        if isinstance(volume_number, list):
                            title = (
                                volume_keyword
                                + str(
                                    convert_array_to_string_with_dashes(volume_number)
                                )
                                + " Part "
                                + str(part)
                            )
                        else:
                            title = (
                                volume_keyword
                                + str(volume_number)
                                + " Part "
                                + str(part)
                            )
                    elif volume_number and not part:
                        if isinstance(volume_number, list):
                            title = volume_keyword + str(
                                convert_array_to_string_with_dashes(volume_number)
                            )
                        else:
                            title = volume_keyword + str(volume_number)
                    if not language and summary:
                        language = detect_language(summary)
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
                        genres,
                        tags,
                    )
                    books.append(book)
                    if limit and len(books) == limit:
                        break
                except Exception as e:
                    send_error_message(e)
                    if hasattr(result, "issue_id"):
                        send_error_message(
                            "\tComic Vine Issue ID: " + str(result.issue_id)
                        )
                    elif issue_id:
                        send_error_message("\tComic Vine Issue ID: " + str(issue_id))
                    write_to_file("comic_vine_errors.txt", str(e))
                    exc_type, exc_obj, exc_tb = sys.exc_info()
                    fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
                    print(exc_type, fname, exc_tb.tb_lineno)
        else:
            print("\t\t\t - No results found!")
    except Exception as e:
        send_error_message(e)
        write_to_file("comic_vine_errors.txt", str(e))
        exc_type, exc_obj, exc_tb = sys.exc_info()
        fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
        print(exc_type, fname, exc_tb.tb_lineno)
    return books


# Credit to original source: https://alamot.github.io/epub_cover/
# Modified by me.
# Retrieves the inner epub cover
def get_epub_cover(epub_path):
    try:
        namespaces = {
            "calibre": "http://calibre.kovidgoyal.net/2009/metadata",
            "dc": "http://purl.org/dc/elements/1.1/",
            "dcterms": "http://purl.org/dc/terms/",
            "opf": "http://www.idpf.org/2007/opf",
            "u": "urn:oasis:names:tc:opendocument:xmlns:container",
            "xsi": "http://www.w3.org/2001/XMLSchema-instance",
        }
        with zipfile.ZipFile(epub_path) as z:
            t = etree.fromstring(z.read("META-INF/container.xml"))
            rootfile_path = t.xpath(
                "/u:container/u:rootfiles/u:rootfile", namespaces=namespaces
            )[0].get("full-path")
            t = etree.fromstring(z.read(rootfile_path))
            cover_id = t.xpath(
                "//opf:metadata/opf:meta[@name='cover']", namespaces=namespaces
            )[0].get("content")
            cover_href = t.xpath(
                "//opf:manifest/opf:item[@id='" + cover_id + "']", namespaces=namespaces
            )[0].get("href")
            if re.search(r"%", cover_href):
                cover_href = urllib.parse.unquote(cover_href)
            cover_path = os.path.join(os.path.dirname(rootfile_path), cover_href)
            return cover_path
        return None
    except Exception as e:
        return None


# remove all non-images from list of files
def remove_non_images(files):
    clean_list = []
    for file in files:
        extension = re.sub(r"\.", "", get_file_extension(os.path.basename(file)))
        if extension in image_extensions:
            clean_list.append(file)
    return clean_list


def find_internal_cover(file, path, extension, root, extensionless_name):
    data = None
    # check if the file is a valid zip file
    extension = "." + extension
    if zipfile.is_zipfile(path):
        epub_cover_path = ""
        if extension == ".epub":
            epub_cover_path = get_epub_cover(path)
            if epub_cover_path:
                epub_cover_path = os.path.basename(epub_cover_path)
                epub_cover_extension = re.sub(
                    r"\.", "", get_file_extension(epub_cover_path)
                )
                if epub_cover_extension not in image_extensions:
                    epub_cover_path = ""
        with zipfile.ZipFile(path, "r") as zip_ref:
            zip_list = zip_ref.namelist()
            zip_list = [
                x
                for x in zip_list
                if not os.path.basename(x).startswith(".")
                and not os.path.basename(x).startswith("__")
            ]
            zip_list = remove_non_images(zip_list)
            # remove anything that isn't a file
            zip_list = [
                x for x in zip_list if not x.endswith("/") and re.search(r"\.", x)
            ]
            # remove any non-supported image files from the list
            for item in zip_list:
                extension = get_file_extension(item)
                extension = re.sub(r"\.", "", extension)
                if extension not in image_extensions:
                    zip_list.remove(item)
            zip_list.sort()
            # parse zip_list and check each os.path.basename for epub_cover_path if epub_cover_path exists, then put it at the front of the list
            if epub_cover_path:
                for item in zip_list:
                    if os.path.basename(item) == epub_cover_path:
                        zip_list.remove(item)
                        zip_list.insert(0, item)
                        break
            if zip_list:
                for image_file in zip_list:
                    if (
                        epub_cover_path
                        and os.path.basename(image_file) == epub_cover_path
                        or re.search(
                            r"(\b(Cover([0-9]+|)|CoverDesign)\b)",
                            image_file,
                            re.IGNORECASE,
                        )
                        or re.search(
                            r"(\b(p000|page_000)\b)", image_file, re.IGNORECASE
                        )
                        or re.search(r"((\s+)0+\.(.{2,}))", image_file, re.IGNORECASE)
                        or re.search(
                            r"(\bindex[-_. ]1[-_. ]1\b)", image_file, re.IGNORECASE
                        )
                        or re.search(
                            r"(9([-_. :]+)?7([-_. :]+)?(8|9)(([-_. :]+)?[0-9]){10})",
                            image_file,
                            re.IGNORECASE,
                        )
                    ):
                        print("\tInternal Cover: " + image_file)
                        with zip_ref.open(image_file) as image_file_ref:
                            data = image_file_ref.read()
                            # close the file
                            image_file_ref.close()
                            return data
                    print("\tNo cover found, defaulting to first image: " + zip_list[0])
                    print("\tInternal Cover: " + image_file)
                    default_cover_path = zip_list[0]
                    with zip_ref.open(default_cover_path) as default_cover_ref:
                        data = default_cover_ref.read()
                        # close the file
                        default_cover_ref.close()
                        return data
    else:
        send_error_message("\nFile: " + file + " is not a valid zip file.")
    return data


# Searches the passes metadata provider
def search_provider(
    file, file_path, multi_volume, extension, provider, zip_comment, dir_files=None
):
    global series_ids_cache
    session_result = None
    epub_path = file_path
    extenionless_name = get_extensionless_name(file)
    cover = find_cover(file_path)
    cover_path = ""
    internal_cover_data = None
    if use_internal_cover:
        internal_cover_data = find_internal_cover(
            file, file_path, extension, root, extenionless_name
        )
    if not cover:
        print("\t\tNo external cover found.")
        if not internal_cover_data and use_internal_cover:
            print("\t\tNo internal cover found.")
            return None
        elif not internal_cover_data and not use_internal_cover:
            print(
                "\t\tuse_internal_cover is disabled and no external cover was found, skipping..."
            )
            return None
        else:
            print("\t\tUsing internal cover")
    else:
        cover_path = os.path.join(root, cover)
        print("\tExternal Cover: " + os.path.basename(cover_path))
        if use_internal_cover:
            print("\n\tUsing internal cover.")
    series = get_series_name_from_file_name(file)
    volume_number = remove_everything_but_volume_num([file])
    if volume_number:
        if not isinstance(volume_number, list):
            volume_number = set_num_as_float_or_int(volume_number)
        else:
            clean_nums = []
            for item in volume_number:
                item = set_num_as_float_or_int(item)
                clean_nums.append(item)
            if clean_nums:
                volume_number = clean_nums
    part = get_volume_part(file)
    part = set_num_as_float_or_int(part)
    directory = os.path.dirname(file_path)
    send_change_message(
        "\nSearching Provider: " + titlecase(remove_underscore_from_name(provider.name))
    )
    if provider.name == "google":
        print("\tSearching folder files for a common series_id...")
        series_files = [
            f
            for f in os.listdir(directory)
            if os.path.isfile(os.path.join(directory, f))
        ]
        if series_files:
            series_files = remove_hidden_files(series_files)
            series_files = remove_non_cbz_epub(series_files)
            in_cache = False
            # check cache to see if the series is already in the cache
            if series_ids_cache and series:
                for item in series_ids_cache:
                    if item.series_name.lower().strip() == series.lower().strip():
                        print("\tFound series in cache!")
                        in_cache = True
                        series_info = item.results
                        session_result = item
                        break
            if not in_cache:
                dir_file_paths = [
                    os.path.join(directory, x)
                    for x in series_files
                    if series_files
                    and x
                    and os.path.isfile(os.path.join(directory, x))
                    and get_series_name_from_file_name(x).lower().strip()
                    == series.lower().strip()
                ]
                dir_file_series_ids = [
                    get_meta_from_file(x, r"series_id:.*", get_file_extension(x))
                    for x in dir_file_paths
                    if dir_file_paths and x
                ]
                # remove empty results from dir_file_series_ids
                dir_file_series_ids = [x for x in dir_file_series_ids if x]
                # remove all duplicates from dir_file_series_ids
                dir_file_series_ids = list(set(dir_file_series_ids))
                series_info = ""
                if len(dir_file_series_ids) == 1:
                    dir_file_series_ids = dir_file_series_ids[0]
                elif dir_file_series_ids and isinstance(dir_file_series_ids, str):
                    dir_file_series_ids = dir_file_series_ids
                else:
                    dir_file_series_ids = ""
                if dir_file_series_ids:
                    dir_file_series_ids = dir_file_series_ids.split("series_id:")[1]
                    series_id_in_cache = False
                    if series_ids_cache:
                        for item in series_ids_cache:
                            if item.series_id == dir_file_series_ids:
                                print("\tFound series_id in cache!")
                                series_id_in_cache = True
                                series_info = item.results
                                session_result = item
                                break
                    elif dir_file_series_ids:
                        print(
                            "\tScraping series info for: id="
                            + dir_file_series_ids
                            + "\n\t\tmay take awhile depending on the number of volumes..."
                        )
                        series_info = scrape_series_ids(dir_file_series_ids)
                        if series_info:
                            session_result = Series_Page_Result(
                                dir_file_series_ids, series, series_info, None
                            )
                        else:
                            print("\tNothing found")
        else:
            print("\tNo other files found in directory for series_id search.")
    if (cover or internal_cover_data) and not skip_image_comparison:
        print("\n----------------------------------------------------------------")
        print("Using string search and image comparison.")
        print("----------------------------------------------------------------")
        cleaned_results = []
        if series and volume_number:
            part = get_volume_part(file)
            volume_number_search_string = ""
            if not isinstance(volume_number, list):
                volume_number_search_string = str(volume_number)
            else:
                volume_number_search_string = str(volume_number[0])
            search = series + " Volume " + volume_number_search_string
            search_two = series + " Vol. " + volume_number_search_string
            search_three = series
            search_four = series + " Volume " + volume_number_search_string
            search_five = series + " " + volume_number_search_string
            if part:
                part = set_num_as_float_or_int(part)
                search += " Part " + str(part)
                search_two += " Part " + str(part)
                search_four += " Part " + str(part)
            if extension == "epub":
                search_four += " Light Novel"
            elif extension == "cbz":
                search_four += " Manga"
            print("\nSearching with: " + search)
            if cover_path and not use_internal_cover:
                print("Cover Image: " + os.path.basename(cover_path))
            print("Required Image SSIM Score: " + str(required_image_ssim_score))
            print("Required Image MSE Score: " + str(required_image_mse_score))
            first_word_in_series = remove_punctuation(series.split(" ")[0])
            if provider.name == "google":
                if series_info and (
                    not session_result or not session_result.api_results
                ):
                    print("\nSearching with all folder series ids")
                    series_search_results = []
                    num = 1
                    print("Total series results: " + str(len(series_info)))
                    for id in series_info:
                        print("\t[" + str(num) + "] " + id)
                        num += 1
                        series_search = google_api_isbn_lookup(
                            0,
                            epub_path,
                            skip_title_check=True,
                            volume_id=id,
                            max_results_num=40,
                        )
                        time.sleep(web_scrape_sleep_time)
                        if series_search:
                            series_search_results.append(series_search)
                    if series_search_results:
                        clean_series_search_results = clean_api_results(
                            series_search_results,
                            volume_number,
                            first_word_in_series,
                            multi_volume,
                            series,
                            extension,
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
                            if session_result:
                                session_result.api_results = clean_series_search_results
                                series_ids_cache.append(session_result)
                            for result in clean_series_search_results:
                                cleaned_results.append(result)
                elif session_result and session_result.api_results:
                    for result in session_result.api_results:
                        if result not in cleaned_results:
                            cleaned_results.append(result)
            if provider.name == "google":
                # check the zip_comment for an isbn number
                if zip_comment:
                    print("\nChecking zip comment for isbn obtained elsewhere...")
                    isbn = search_for_isbn(zip_comment, file)
                    if isbn:
                        print(
                            "\tFound isbn in zip comment: "
                            + str(isbn.isbn)
                            + " , adding to list of results."
                        )
                        clean_google_result = clean_api_results(
                            [isbn],
                            volume_number,
                            first_word_in_series,
                            multi_volume,
                            series,
                            extension,
                            skip_series_similarity=True,
                            skip_vol_nums_equal=True,
                            skip_categories_check=True,
                        )
                        for result in clean_google_result:
                            if result not in cleaned_results:
                                cleaned_results.append(result)
            if provider.name == "google":
                r = google_api_isbn_lookup(
                    0,
                    epub_path,
                    search,
                    skip_title_check=True,
                    in_line_search=False,
                    type=extension,
                    number=volume_number,
                )
                if r:
                    clean_r_results = clean_api_results(
                        r,
                        volume_number,
                        first_word_in_series,
                        multi_volume,
                        series,
                        extension,
                        skip_contains_first_word=True,
                        skip_vol_nums_equal=True,
                    )
                    for result in clean_r_results:
                        if result not in cleaned_results:
                            cleaned_results.append(result)
            # if provider.name == "google":
            #     print("\nAdditional volume quoted search: " + search)
            #     b = google_api_isbn_lookup(
            #         0,
            #         epub_path,
            #         search,
            #         skip_title_check=True,
            #         in_line_search=False,
            #         type=extension,
            #         number=volume_number,
            #         quoted_search=True,
            #     )
            #     if b:
            #         clean_b_results = clean_api_results(
            #             b,
            #             volume_number,
            #             first_word_in_series,
            #             multi_volume,
            #             series,
            #             extension,
            #             skip_contains_first_word=True,
            #             skip_vol_nums_equal=True,
            #         )
            #         for result in clean_b_results:
            #             if result not in cleaned_results:
            #                 cleaned_results.append(result)
            if provider.name == "google" and not limit_google_search:
                print("\nAdditional Search without volume Keyword: " + search_three)
                no_volume_keyword_results = google_api_isbn_lookup(
                    0,
                    epub_path,
                    search_three,
                    max_results_num=30,
                    skip_title_check=True,
                    in_line_search=False,
                    type=extension,
                )
                if no_volume_keyword_results:
                    clean_no_volume_keyword_results = clean_api_results(
                        no_volume_keyword_results,
                        volume_number,
                        first_word_in_series,
                        multi_volume,
                        series,
                        extension,
                        skip_series_similarity=True,
                        skip_vol_nums_equal=True,
                        skip_omnibus_check=True,
                    )
                    for result in clean_no_volume_keyword_results:
                        if result not in cleaned_results:
                            cleaned_results.append(result)
                print(
                    "\nAdditional Search without volume Keyword: "
                    + search_three
                    + ", with no category check and limited to three results."
                )
                no_volume_keyword_results_no_cat = google_api_isbn_lookup(
                    0,
                    epub_path,
                    search_three,
                    max_results_num=3,
                    skip_title_check=True,
                    in_line_search=True,
                    type=extension,
                )
                if no_volume_keyword_results_no_cat:
                    clean_no_volume_keyword_results_no_cat = clean_api_results(
                        no_volume_keyword_results,
                        volume_number,
                        first_word_in_series,
                        multi_volume,
                        series,
                        extension,
                        skip_series_similarity=True,
                        skip_vol_nums_equal=True,
                        skip_categories_check=True,
                    )
                    for result in clean_no_volume_keyword_results_no_cat:
                        if result not in cleaned_results:
                            cleaned_results.append(result)
            if provider.name == "kobo":
                print("\nSearching Kobo with: " + search)
                kobo_results = []
                search_with_and_instead_of_amp = re.sub(r"&", "and", search)
                kobo_search_results = text_search_kobo(search)
                kobo_search_with_and = text_search_kobo(search_with_and_instead_of_amp)
                # limit total web scraping to 5 results
                kobo_search_results = kobo_search_results[:5]
                kobo_search_with_and = kobo_search_with_and[:5]
                # extend kobo_search_results with kobo_search_with_and
                kobo_search_results.extend(kobo_search_with_and)
                # remove all results after 5
                if kobo_search_results:
                    for kobo_r in kobo_search_results:
                        data_result = get_kobo_books_meta(
                            kobo_r, 0, None, None, text_search=True
                        )
                        if data_result and data_result not in kobo_results:
                            kobo_results.append(data_result)
                        print(
                            "\n\t\tSleeping for "
                            + str(web_scrape_sleep_time)
                            + " seconds...\n"
                        )
                        time.sleep(web_scrape_sleep_time)
                else:
                    print("\tNo results found.")
                if kobo_results:
                    clean_kobo_results = clean_api_results(
                        kobo_results,
                        volume_number,
                        first_word_in_series,
                        multi_volume,
                        series,
                        extension,
                        skip_series_similarity=True,
                        skip_vol_nums_equal=True,
                        skip_omnibus_check=True,
                        skip_categories_check=True,
                    )
                    for result in clean_kobo_results:
                        if result not in cleaned_results:
                            cleaned_results.append(result)
            if provider.name == "bookwalker":
                bw_category = None
                if extension == "epub":
                    bw_category = "l"
                elif extension == "cbz":
                    bw_category = "m"
                bookwalker_results = []
                print("\nSearching Bookwalker with: " + search_five)
                bookwalker_search_results = text_search_bookwalker(
                    search_five, bw_category
                )
                if bookwalker_search_results:
                    for bookwalker_r in bookwalker_search_results:
                        data_result = get_bookwalker_books_meta(bookwalker_r)
                        if data_result and data_result not in bookwalker_results:
                            bookwalker_results.append(data_result)
                        print(
                            "\n\t\tSleeping for "
                            + str(web_scrape_sleep_time)
                            + " seconds...\n"
                        )
                        time.sleep(web_scrape_sleep_time)
                else:
                    print("\tNo results found.")
                print(
                    "\nSearching Bookwalker with: "
                    + search_three
                    + "\n\tLimit: 5 results"
                )
                no_volume_number_series_search_results = text_search_bookwalker(
                    search_three, bw_category, 5
                )
                if no_volume_number_series_search_results:
                    for bookwalker_r in no_volume_number_series_search_results:
                        data_result = get_bookwalker_books_meta(bookwalker_r)
                        if data_result and data_result not in bookwalker_results:
                            bookwalker_results.append(data_result)
                        print(
                            "\n\t\tSleeping for "
                            + str(web_scrape_sleep_time)
                            + " seconds...\n"
                        )
                        time.sleep(web_scrape_sleep_time)
                if bookwalker_results:
                    clean_bookwalker_results = clean_api_results(
                        bookwalker_results,
                        volume_number,
                        first_word_in_series,
                        multi_volume,
                        series,
                        extension,
                        skip_series_similarity=True,
                        skip_vol_nums_equal=True,
                        skip_omnibus_check=True,
                        skip_categories_check=True,
                    )
                    for result in clean_bookwalker_results:
                        if result not in cleaned_results:
                            cleaned_results.append(result)
            results_with_image_score = []
            if provider.name == "barnes_and_noble":
                barnes_results = []
                print("\nSearching Barnes and Noble with: " + search_five)
                bn_search_results = text_search_barnes_and_noble(search_five)
                if bn_search_results and isinstance(bn_search_results, list):
                    for bn_r in bn_search_results:
                        data_result = get_barnes_and_noble_books_meta(bn_r)
                        if data_result and data_result not in barnes_results:
                            barnes_results.append(data_result)
                        print(
                            "\n\tSleeping for "
                            + str(web_scrape_sleep_time)
                            + " seconds...\n"
                        )
                        time.sleep(web_scrape_sleep_time)
                elif bn_search_results and hasattr(bn_search_results, "isbn"):
                    barnes_results = [bn_search_results]
                else:
                    print("\tNo search results found")
                if barnes_results:
                    clean_barnes_results = clean_api_results(
                        barnes_results,
                        volume_number,
                        first_word_in_series,
                        multi_volume,
                        series,
                        extension,
                        skip_series_similarity=True,
                        skip_vol_nums_equal=True,
                        skip_omnibus_check=True,
                        skip_categories_check=True,
                    )
                    for result in clean_barnes_results:
                        if result not in cleaned_results:
                            cleaned_results.append(result)
            if (
                provider.name == "comic_vine"
                and comic_vine_api_key
                and extension == "cbz"
            ):
                comic_vine_results = []
                print("\nSearching Comic Vine with: " + search_five)
                comic_vine_results = search_comic_vine(search_five, comic_vine_api_key)
                print(
                    "\n\tSleeping for " + str(comic_vine_sleep_time) + " seconds...\n"
                )
                time.sleep(comic_vine_sleep_time)
                if comic_vine_results:
                    clean_comic_vine_results = clean_api_results(
                        comic_vine_results,
                        volume_number,
                        first_word_in_series,
                        multi_volume,
                        series,
                        extension,
                        skip_series_similarity=False,
                        skip_vol_nums_equal=True,
                        skip_omnibus_check=True,
                        skip_categories_check=True,
                        series_similarity_score=0.8,
                    )
                    if clean_comic_vine_results:
                        clean_comic_vine_results = clean_comic_vine_results[:5]
                        for result in clean_comic_vine_results:
                            if result not in cleaned_results:
                                cleaned_results.append(result)
            # remove any duplicate results from cleaned_results
            cleaned_results = list(dict.fromkeys(cleaned_results))
            if cleaned_results:
                print("\nTotal results: " + str(len(cleaned_results)))
                for result in cleaned_results:
                    try:
                        print(
                            "\tResult "
                            + str(cleaned_results.index(result) + 1)
                            + " of "
                            + str(len(cleaned_results))
                            + ":"
                        )
                        print("\t\tSeries: " + result.series)
                        print("\t\tVolume: " + str(result.volume))
                        print("\t\tISBN: " + str(result.isbn))
                        print("\t\tLink: " + result.preview_link[0])
                        if result.image_links:
                            print(
                                "\t\tTotal Image Links: " + str(len(result.image_links))
                            )
                            if not multi_process_image_links:
                                for link in result.image_links:
                                    image_result = process_image_link(
                                        result, cover_path, link, internal_cover_data
                                    )
                                    if image_result:
                                        results_with_image_score.append(image_result)
                            else:
                                with concurrent.futures.ThreadPoolExecutor() as executor:
                                    worker = partial(
                                        process_image_link,
                                        result,
                                        cover_path,
                                        internal_cover_data,
                                    )
                                    results = executor.map(
                                        worker,
                                        result.image_links,
                                    )
                                    if results:
                                        for result in results:
                                            results_with_image_score.append(result)
                    except Exception as e:
                        send_error_message(e)
                        write_to_file("isbn_script_errors.txt", str(e))
                        exc_type, exc_obj, exc_tb = sys.exc_info()
                        fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
                        print(exc_type, fname, exc_tb.tb_lineno)
                        continue
            else:
                send_error_message("\tNo results left after heavy filtering.")
            if results_with_image_score:
                results_with_image_score.sort(
                    key=lambda x: x.ssim_score,
                    reverse=True,
                )
                best_result = results_with_image_score[0]
                if (
                    best_result.ssim_score >= required_image_ssim_score
                    or best_result.mse_score <= required_image_mse_score
                ):
                    best_result.book.series = series
                    best_result.book.volume_number = volume_number
                    best_result.book.number = volume_number
                    best_result.book.volume = volume_number
                    best_result.book.part = part
                    if re.search(
                        r"Volumes?",
                        best_result.book.title,
                        re.IGNORECASE,
                    ):
                        volume_keyword = ""
                        if isinstance(best_result.book.volume_number, list):
                            volume_keyword = "Volumes "
                            best_result.book.title = volume_keyword + str(
                                convert_array_to_string_with_dashes(volume_number)
                            )
                        else:
                            volume_keyword = "Volume "
                            best_result.book.title = volume_keyword + str(volume_number)
                        if part:
                            best_result.book.title = (
                                best_result.book.title + " Part " + str(part)
                            )
                    if not best_result.book.title and volume_number and part:
                        volume_keyword = ""
                        if isinstance(best_result.book.volume_number, list):
                            volume_keyword = "Volumes "
                            best_result.book.title = (
                                volume_keyword
                                + str(
                                    convert_array_to_string_with_dashes(volume_number)
                                )
                                + " Part "
                                + str(part)
                            )
                        else:
                            volume_keyword = "Volume "
                            best_result.book.title = (
                                volume_keyword
                                + str(volume_number)
                                + " Part "
                                + str(part)
                            )
                    elif not best_result.book.title and volume_number and not part:
                        volume_keyword = ""
                        if isinstance(best_result.book.volume_number, list):
                            volume_keyword = "Volumes "
                            best_result.book.title = volume_keyword + str(
                                convert_array_to_string_with_dashes(volume_number)
                            )
                        else:
                            volume_keyword = "Volume "
                            best_result.book.title = volume_keyword + str(volume_number)
                    print("\t\tSeries: " + best_result.book.series)
                    if best_result.book.title:
                        send_discord_message("Title: " + best_result.book.title)
                    if best_result.book.publisher:
                        send_discord_message("Publisher: " + best_result.book.publisher)
                    if best_result.book.published_date:
                        send_discord_message(
                            "Release Date: " + best_result.book.published_date
                        )
                    if best_result.book.summary:
                        send_discord_message("Summary: " + best_result.book.summary)
                    if best_result.book.preview_link:
                        send_change_message(
                            "\t\tLink: " + best_result.book.preview_link[0]
                        )
                    if best_result.image_link:
                        send_change_message("\t\tImage Link: " + best_result.image_link)
                    if best_result.book.api_link:
                        send_change_message(
                            "\t\tAPI Link: " + best_result.book.api_link
                        )
                    if best_result.book.volume_number:
                        print(
                            "\t\tVolume Number: " + str(best_result.book.volume_number)
                        )
                    if best_result.ssim_score:
                        send_change_message("\t\tSSIM: " + str(best_result.ssim_score))
                    if best_result.psnr_score:
                        print("\t\tPSNR: " + str(best_result.psnr_score))
                    if best_result.mse_score:
                        send_change_message("\t\tMSE: " + str(best_result.mse_score))
                    if best_result.book.part:
                        print("\t\tPart: " + str(best_result.book.part))
                    write_to_file(
                        "items_found_through_image_comparision_search.txt",
                        epub_path,
                    )
                    return best_result
                else:
                    send_error_message(
                        "\tHighest SSIM Score "
                        + str(best_result.ssim_score)
                        + " is less than the required score of "
                        + str(required_image_ssim_score)
                        + "\n\tand the lowest MSE Score "
                        + str(best_result.mse_score)
                        + " is greater than the required score of "
                        + str(required_image_mse_score)
                    )
                    if best_result.psnr_score:
                        print("\tPSNR Score: " + str(best_result.psnr_score))
                    if best_result.image_link:
                        print("\tImage Link: " + best_result.image_link)
                    if best_result.book.api_link:
                        print("\tAPI Link: " + best_result.book.api_link)
                    if best_result.book.series:
                        print("\tSeries: " + best_result.book.series)
                    # if best_result.book.volume:
                    #     print("\tVolume: " + str(best_result.book.volume))
                    if best_result.book.isbn:
                        print("\tISBN: " + str(best_result.book.isbn))
                    if best_result.book.preview_link:
                        print("\tLink: " + best_result.book.preview_link[0])
                    write_to_file(
                        "items_not_found_through_image_comparision_search.txt",
                        epub_path,
                        without_date=True,
                    )
                    items_not_found_through_image_comparision_search.append(epub_path)
                    if extension == "epub" and not multi_volume:
                        num = volume_number
                        if isinstance(num, list):
                            num = num[0]
                        data = get_metadata_from_epub_via_calibre(epub_path)
                        if part:
                            num = str(num) + "." + str(part)
                            num = float(num)
                        if num != data.number:
                            update_metadata(
                                "ebook-meta",
                                epub_path,
                                None,
                                num,
                                "Index Number",
                                "-i",
                                skip_print=True,
                            )
                        if series != data.series:
                            update_metadata(
                                "ebook-meta",
                                epub_path,
                                data.series,
                                series,
                                "Series",
                                "--series",
                                skip_print=True,
                            )
            else:
                # send_error_message("\tNo image score results.")
                write_to_file(
                    "items_not_found_through_image_comparision_search.txt",
                    epub_path,
                    without_date=True,
                )
                items_not_found_through_image_comparision_search.append(epub_path)
                if extension == "epub" and not multi_volume:
                    num = volume_number
                    if isinstance(num, list):
                        num = num[0]
                    data = get_metadata_from_epub_via_calibre(epub_path)
                    if part:
                        num = str(num) + "." + str(part)
                        num = float(num)
                    if num != data.number:
                        update_metadata(
                            "ebook-meta",
                            epub_path,
                            None,
                            num,
                            "Index Number",
                            "-i",
                            skip_print=True,
                        )
                    if series != data.series:
                        update_metadata(
                            "ebook-meta",
                            epub_path,
                            data.series,
                            series,
                            "Series",
                            "--series",
                            skip_print=True,
                        )
    else:
        if not cover:
            send_error_message("No cover image found for " + epub_path)
        if skip_image_comparison:
            send_error_message("skip_image_comparison=True, skipping...")
        write_to_file(
            "items_not_found_through_image_comparision_search.txt",
            epub_path,
            without_date=True,
        )
        items_not_found_through_image_comparision_search.append(epub_path)
        if extension == "epub" and not multi_volume:
            num = volume_number
            if isinstance(num, list):
                num = num[0]
            data = get_metadata_from_epub_via_calibre(epub_path)
            if part:
                num = str(num) + "." + str(part)
                num = float(num)
            if num != data.number:
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    None,
                    num,
                    "Index Number",
                    "-i",
                    skip_print=True,
                )
            if series != data.series:
                update_metadata(
                    "ebook-meta",
                    epub_path,
                    data.series,
                    series,
                    "Series",
                    "--series",
                    skip_print=True,
                )
    return None


# open ComicInfo.xml from the passed zip file, and return the xml contents as a string
def get_comic_info_xml(zip_file):
    with zipfile.ZipFile(zip_file, "r") as z:
        with z.open("ComicInfo.xml", "r") as f:
            return f.read().decode("utf-8")


# check if zip file contains ComicInfo.xml
def check_if_zip_file_contains_comic_info_xml(zip_file):
    with zipfile.ZipFile(zip_file, "r") as zip_ref:
        list = zip_ref.namelist()
        for name in list:
            if os.path.basename(name).lower() == "ComicInfo.xml".lower():
                return True
    return False


# check if the date is in the past
def check_if_date_is_past(day, month, year):
    if day or month or year:
        today = datetime.today()
        if not day:
            day = today.day
        else:
            day = int(day)
        if not month:
            month = today.month
        else:
            month = int(month)
        if not year:
            year = today.year
        else:
            year = int(year)
        if day and month and year:
            try:
                date = datetime(year, month, day)
                if date < today:
                    return True
            except ValueError:
                return False
        else:
            return False
    else:
        return False


# get age of file and return in minutes based on modification time
def get_modiciation_age(file):
    return int(time.time() - os.path.getmtime(file)) / 60


# get age of file and return in minutes based on creation time
def get_creation_age(file):
    return int(time.time() - os.path.getctime(file)) / 60


# regex out underscore from passed string and return it
def remove_underscore_from_name(name):
    name = re.sub(r"_", " ", name)
    name = remove_dual_space(name).strip()
    return name


def process_file(file_name, files):
    file_path = os.path.join(root, file_name)
    zip_comments = str(get_zip_comment(file_path))
    extension = get_file_extension(file_name)
    if skip_volumes_older_than_x_time and os.path.isfile(file_path):
        modification_age = get_modiciation_age(file_path)
        creation_age = get_creation_age(file_path)
        if modification_age >= 60 and creation_age >= 60:
            print("Skipping because it is older than 60 minutes")
            return None
    try:
        multi_volume = check_for_multi_volume_file(file_name)
        volume_number = remove_everything_but_volume_num([file_name])
        if not isinstance(volume_number, list):
            if skip_non_volume_ones and volume_number != 1:
                print("\tSkip non-volume one files enabled, skipping: " + file_name)
                return None
        elif isinstance(volume_number, list):
            if skip_non_volume_ones and 1 not in volume_number:
                print("\tSkip non-volume one files enabled, skipping: " + file_name)
                return None
        if skip_volume_if_already_has_anilist_id:
            if zip_comments and re.search(r"anilist_id", zip_comments, re.IGNORECASE):
                print("Skipping " + file_name + " because it already has an anilist_id")
                return None
            elif extension == "epub" and get_meta_from_file(
                file_path, r"(\<dc\:subject\>)", extension
            ):
                print(
                    "\tSkipping " + file_name + " because it already has an anilist_id"
                )
                return None
        if extension in accepted_file_types:
            result = ""
            if extension == "cbz":
                contains_comic_info = check_if_zip_file_contains_comic_info_xml(
                    file_path
                )
                if contains_comic_info:
                    comic_info_contents = get_comic_info_xml(file_path)
                    if (
                        skip_all_non_comic_tagger_tagged
                        and not skip_if_file_contains_comic_info
                    ):
                        if comic_info_contents:
                            if not re.search(
                                r"ComicTagger", comic_info_contents, re.IGNORECASE
                            ):
                                print("\tnot tagged by comictagger, skipping...")
                                return None
                    if skip_google_metadata and comic_info_contents:
                        if re.search(r"googleapis", comic_info_contents, re.IGNORECASE):
                            print("\tcontains google metadata, skipping...")
                            return None
                elif (
                    not contains_comic_info
                    and skip_all_non_comic_tagger_tagged
                    and not skip_if_file_contains_comic_info
                ):
                    print("\tno comicinfo contents found, skipping")
                    return None
                if skip_file_if_isbn_in_zip_comment:
                    if re.search(rf"{isbn_13_regex}", zip_comments):
                        print("\n" + file_name + " already contains isbn, skipping...")
                        print("\t" + zip_comments)
                        return None
                elif skip_if_file_contains_comic_info and contains_comic_info:
                    print("\t" + " already contains ComicInfo.xml, skipping...")
                    return None
            elif extension == "epub":
                if skip_novels_with_metadata:
                    contains_title = check_epub_for_title(file_path)
                    if contains_title:
                        print("\t" + " already contains metadata, skipping...")
                        return None
            send_discord_message(
                "\n--------------------------------------------------------------------------------\n"
                + "File: "
                + os.path.basename(file)
                + "\n--------------------------------------------------------------------------------"
            )
            for provider in providers:
                if provider.enabled:
                    result = search_provider(
                        file_name,
                        file_path,
                        multi_volume,
                        extension,
                        provider,
                        zip_comments,
                        dir_files=files,
                    )
                    if result:
                        break
                else:
                    print("\t" + provider.name + " is disabled, skipping...")
            if not result and (not only_image_comparision or extension == "cbz"):
                print(
                    "----------------------------------------------------------------"
                )
                print("BACKUP: Searching Internal Contents for an ISBN...")
                print(
                    "----------------------------------------------------------------"
                )
                result = zip_file_stuff(file_path)
            if result and hasattr(result, "book"):
                # get today's day from today's date
                todays_day = datetime.now().strftime("%d")
                if todays_day:
                    todays_day = int(todays_day)
                else:
                    todays_day = ""
                if result.book.published_date and re.search(
                    r"-", result.book.published_date
                ):
                    if re.search(
                        r"((\d\d\d\d)-(\d+)-(\d+))", result.book.published_date
                    ):
                        day = result.book.published_date.split("-")[2]
                    else:
                        day = result.book.published_date.split("-")[1]
                else:
                    day = ""
                if day:
                    day = int(day)
                else:
                    day = ""
                if (
                    (
                        result.book.is_ebook
                        and result.book.for_sale
                        and result.book.for_sale == "FOR_SALE"
                    )
                    or (
                        not check_if_date_is_past(
                            result.book.day, result.book.month, result.book.year
                        )
                        and todays_day
                        and day
                        and day == todays_day + 1
                    )
                    or (
                        square_enix_bypass
                        and re.search(r"Square", result.book.publisher, re.IGNORECASE)
                        and re.search(r"Enix", result.book.publisher, re.IGNORECASE)
                    )
                    or (
                        result.book.day
                        and result.book.month
                        and result.book.year
                        and is_future_date(
                            int(result.book.day),
                            int(result.book.month),
                            int(result.book.year),
                        )
                    )
                ):
                    if result.book.summary:
                        # send_discord_message("Title: " + result.book.title)
                        # send_discord_message("Summary: " + result.book.summary)
                        # send_discord_message("Link: " + result.book.preview_link[0])
                        # send_discord_message(
                        #     "Image Link: " + result.book.image_links[1]
                        # )
                        write_metadata = compare_metadata(result.book, file_path, files)
                        items_found_through_ocr_on_epub.append(file_path)
                        write_to_file(
                            "items_found_through_ocr_on_epub.txt",
                            file_path,
                        )
                        return result
                    elif not result.book.summary and scrape_kobo:
                        send_error_message(
                            "api result has no summary, attempting to use an alternative source..."
                        )
                        kobo_alt_result = get_kobo_books_meta(
                            "https://www.kobo.com",
                            result.book.isbn,
                            result.book.volume,
                            result.book.part,
                            result.book.series,
                        )
                        if kobo_alt_result and kobo_alt_result.summary:
                            send_change_message(
                                "\tResult found with alternative source: "
                                + kobo_alt_result.api_link
                            )
                            send_change_message("\t\tTitle: " + kobo_alt_result.title)
                            send_change_message(
                                "\t\tPublisher: " + kobo_alt_result.publisher
                            )
                            send_change_message(
                                "\t\tSummary: " + kobo_alt_result.summary
                            )
                            send_change_message("\t\tLink: " + kobo_alt_result.api_link)
                            send_change_message(
                                "\t\tImage Link: " + kobo_alt_result.image_links[0]
                            )
                            write_metadata = compare_metadata(
                                kobo_alt_result, file_path, files
                            )
                            items_found_through_ocr_on_epub.append(file_path)
                            write_to_file(
                                "items_found_through_ocr_on_epub.txt",
                                file_path,
                            )
                            return kobo_alt_result
                        else:
                            send_error_message("\tno kobo result, skipping...")
                    else:
                        send_error_message("\tempty summary, skipping...")
                else:
                    send_error_message(
                        "\tFile: " + file_name + "\n\t\tis_ebook=False\n\t\tskipping..."
                    )
    except Exception as e:
        send_error_message(e)
        write_to_file("isbn_script_errors.txt", str(e))
        exc_type, exc_obj, exc_tb = sys.exc_info()
        fname = os.path.split(exc_tb.tb_frame.f_code.co_filename)[1]
        print(exc_type, fname, exc_tb.tb_lineno)
    return None


if __name__ == "__main__":
    parser = image_arg_parser()
    args = parser.parse_args()
    if args.webhook is not None:
        for item in args.webhook:
            for hook in item:
                if hook not in discord_webhook_url:
                    discord_webhook_url.append(hook)
    if args.accepted_file_types:
        if re.search(r",", args.accepted_file_types):
            accepted_file_types = args.accepted_file_types.split(",")
        else:
            accepted_file_types = [args.accepted_file_types]
    if args.skip_file_if_isbn_in_zip_comment:
        if args.skip_file_if_isbn_in_zip_comment.lower().strip() == "true":
            skip_file_if_isbn_in_zip_comment = True
        else:
            skip_file_if_isbn_in_zip_comment = False
    if args.skip_all_non_comic_tagger_tagged:
        if args.skip_all_non_comic_tagger_tagged.lower().strip() == "true":
            skip_all_non_comic_tagger_tagged = True
        else:
            skip_all_non_comic_tagger_tagged = False
    if args.only_image_comparision:
        if args.only_image_comparision.lower() == "true":
            only_image_comparision = True
        elif args.only_image_comparision.lower() == "false":
            only_image_comparision = False
    if args.skip_letters:
        skip_letters = True
        accepted_letters = args.skip_letters
    if args.skip_comic_info:
        if args.skip_comic_info.lower() == "true":
            skip_if_file_contains_comic_info = True
    if args.manualmetadata:
        if args.manualmetadata == "True" or args.manualmetadata == "true":
            manual_metadata_write_approval = True
        else:
            manual_metadata_write_approval = False
    if args.skip_novels_with_metadata:
        if args.skip_novels_with_metadata.lower() == "true":
            skip_novels_with_metadata = True
        else:
            skip_novels_with_metadata = False
    if args.skip_non_volume_ones:
        if args.skip_non_volume_ones.lower() == "true":
            skip_non_volume_ones = True
        else:
            skip_non_volume_ones = False
    if args.skip_volumes_older_than_x_time:
        if args.skip_volumes_older_than_x_time.lower() == "true":
            skip_volumes_older_than_x_time = True
        else:
            skip_volumes_older_than_x_time = False
    if args.scrape_google:
        # find google provider in providers list
        if args.scrape_google.lower() == "true":
            for provider in providers:
                if provider.name == "google":
                    provider.enabled = True
                    break
        elif args.scrape_google.lower() == "false":
            for provider in providers:
                if provider.name == "google":
                    provider.enabled = False
                    break
    if args.scrape_bookwalker:
        # find bookwalker provider in providers list
        if args.scrape_bookwalker.lower() == "true":
            for provider in providers:
                if provider.name == "bookwalker":
                    provider.enabled = True
                    break
        elif args.scrape_bookwalker.lower() == "false":
            for provider in providers:
                if provider.name == "bookwalker":
                    provider.enabled = False
                    break
    if args.scrape_kobo:
        # find kobo provider in providers list
        if args.scrape_kobo.lower() == "true":
            for provider in providers:
                if provider.name == "kobo":
                    provider.enabled = True
                    break
        elif args.scrape_kobo.lower() == "false":
            for provider in providers:
                if provider.name == "kobo":
                    provider.enabled = False
                    break
    if args.scrape_barnes_and_noble:
        # find barnes and noble provider in providers list
        if args.scrape_barnes_and_noble.lower() == "true":
            for provider in providers:
                if provider.name == "barnes_and_noble":
                    provider.enabled = True
                    break
        elif args.scrape_barnes_and_noble.lower() == "false":
            for provider in providers:
                if provider.name == "barnes_and_noble":
                    provider.enabled = False
                    break
    if args.scrape_comic_vine:
        # find comic vine provider in providers list
        if args.scrape_comic_vine.lower() == "true":
            for provider in providers:
                if provider.name == "comic_vine":
                    provider.enabled = True
                    break
        elif args.scrape_comic_vine.lower() == "false":
            for provider in providers:
                if provider.name == "comic_vine":
                    provider.enabled = False
                    break
    if args.skip_volume_if_already_has_anilist_id:
        if args.skip_volume_if_already_has_anilist_id.lower() == "true":
            skip_volume_if_already_has_anilist_id = True
        elif args.skip_volume_if_already_has_anilist_id.lower() == "false":
            skip_volume_if_already_has_anilist_id = False
        else:
            skip_volume_if_already_has_anilist_id = False
    if args.skip_google_metadata:
        if args.skip_google_metadata.lower() == "true":
            skip_google_metadata = True
        elif args.skip_google_metadata.lower() == "false":
            skip_google_metadata = False
        else:
            skip_google_metadata = False
    if args.use_internal_cover:
        if args.use_internal_cover.lower() == "true":
            use_internal_cover = True
        elif args.use_internal_cover.lower() == "false":
            use_internal_cover = False
    stop = False
    if args.path or args.file:
        # args.file = "/srv/dev-disk-by-uuid-4da94d03-b430-471f-af24-6a27bf7fee2e/manga/public/World's End Harem - Fantasia/World's End Harem - Fantasia v07 (2022) (Digital) (LuCaZ).cbz"
        if args.file:
            args.path = os.path.dirname(args.file)
        if os.path.exists(args.path):
            # args.path = "/srv/dev-disk-by-uuid-4da94d03-b430-471f-af24-6a27bf7fee2e/novels/public/The Fruit of Evolution - Before I Knew It, My Life Had It Made!"
            os.chdir(args.path)
            for root, dirs, files in scandir.walk(args.path, topdown=True):
                if skip_letters and root == args.path:
                    dirs[:] = [
                        d
                        for d in dirs
                        if re.search(accepted_letters, d[0], re.IGNORECASE)
                    ]
                if args.file:
                    files = [os.path.basename(args.file)]
                if args.sort and args.sort.lower() == "true":
                    dirs.sort()
                    files.sort()
                remove_ignored_folders(dirs)
                dirs = remove_hidden_folders(dirs)
                files = remove_hidden_files(files)
                files = remove_non_cbz_epub(files)
                result = None
                if files and not stop:
                    if multi_process_files and len(files) > 1:
                        with concurrent.futures.ThreadPoolExecutor(
                            max_workers=2
                        ) as executer:
                            result = executer.map(process_file, files)
                        if args.file:
                            stop = True
                    else:
                        for file in files:
                            print(
                                "\n--------------------------------------------------------------------------------\n"
                                + "File: "
                                + os.path.basename(file)
                                + "\n--------------------------------------------------------------------------------"
                            )
                            process_result = process_file(file, files)
                            if args.file:
                                stop = True
                                break
                elif stop:
                    break
        else:
            send_error_message("Directory does not exist: " + args.path)
    else:
        send_error_message("No image path or zip file provided")
