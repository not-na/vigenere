#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
#  vigenere
#  
#  Copyright 2018 notna <notna@apparat.org>
#  
#  This file is part of vigenere.
#
#  vigenere is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 3 of the License, or
#  (at your option) any later version.
#
#  vigenere is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with vigenere.  If not, see <http://www.gnu.org/licenses/>.
import collections
import math
import operator
import os
import string
import itertools
import functools
import time
from typing import List, Dict, Tuple

try:
    import pyperclip
    HAVE_PYPERCLIP = True
except ImportError:
    pyperclip = None
    HAVE_PYPERCLIP = False

ALPHABET = string.ascii_uppercase

# Heavily impacts performance, but may be necessary for more difficult texts
MIN_NGRAM = 3
MAX_NGRAM = 16
MAX_KEYLENGTH = 16

MOST_COMMON_LETTER = "E"  # Applicable for almost all languages using the latin alphabet

VERBOSITY = 2


# Prime Factorization from https://stackoverflow.com/a/412942

def prime_factors(n: int) -> List[int]:
    """Returns all the prime factors of a positive integer"""
    factors = []
    d = 2
    while n > 1:
        while n % d == 0:
            factors.append(int(d))
            n /= d
        d = d + 1
        if d*d > n:
            if n > 1:
                factors.append(int(n))
            break
    return factors


# Standard Vigenere Encryption/Decryption functions

def normalize_text(text: str) -> str:
    return "".join([char for char in text.upper() if char in ALPHABET])


def encrypt(plain: str, key: str) -> str:
    plain = normalize_text(plain)
    cypher = ""

    key_offsets = [ALPHABET.index(char) for char in normalize_text(key)]

    for i in range(len(plain)):
        cypher += ALPHABET[(ALPHABET.index(plain[i]) + key_offsets[i % len(key)]) % len(ALPHABET)]

    return cypher


def decrypt(cypher: str, key: str) -> str:
    cypher = normalize_text(cypher)
    plain = ""

    key_offsets = [ALPHABET.index(char) for char in normalize_text(key)]

    for i in range(len(cypher)):
        plain += ALPHABET[(ALPHABET.index(cypher[i]) - key_offsets[i % len(key)]) % len(ALPHABET)]

    return plain


# Cracking Functions

def find_multiples(cypher: str, verbosity=0) -> Dict[str, List[int]]:
    # Returns a dict of ngram:list of positions
    multiples = {}  # Dict of ngram:list of positions

    for i in range(len(cypher)):

        # Add all ngrams ending with the current character
        for n in range(MIN_NGRAM, MAX_NGRAM+1):
            if n > i+1:
                continue

            pos = i - n + 1
            ngram = cypher[i-n+1:i+1]  # Gets the substring starting with the nth char before i and ending at i

            if ngram not in multiples:
                multiples[ngram] = []
            elif verbosity >= 4:
                print("Multiple: "+ngram)

            multiples[ngram].append(pos)

    return {ngram: positions for ngram, positions in multiples.items() if len(positions) > 1}


def calc_distances(multiples: Dict[str, List], verbosity=0) -> List[int]:
    distances = []  # Plain list of distances

    for ngram, positions in multiples.items():
        for i in range(2, len(positions)):
            distances.extend(
                positions[i]-j for j in positions[:i]
            )

    return distances


def find_common_divisors(distances: List[int], verbosity=0) -> Dict[int, int]:
    factor_cache = {}

    if verbosity >= 2:
        print("Factoring all distances...")

    divisors = []  # List of lists of divisors
    for distance in distances:
        if distance not in factor_cache:
            factor_cache[distance] = sorted(prime_factors(distance))
        divisors.append(factor_cache[distance])

    del factor_cache  # Save some memory

    if verbosity >= 2:
        print("Finding common divisors by permutating prime factors...")

    div_freqs = {}  # dict of divisor:number of occurances

    for divs in divisors:
        old = set()
        for r in range(1, len(divs)):
            for c in itertools.permutations(divs, r):
                t = tuple(sorted(c))
                if t in old:
                    continue  # Prevents double-processing
                old.add(t)

                prod = functools.reduce(operator.mul, c)
                if prod not in div_freqs:
                    div_freqs[prod] = 0
                div_freqs[prod] += 1

    return div_freqs


def crack(cypher: str, verbosity=0) -> Tuple[str, str]:
    cypher = normalize_text(cypher)

    # First Part of cracking algorithm
    # Uses the Kasiski Test to find the length of the key
    if verbosity >= 2:
        print("Finding common ngrams...")
    multiples = find_multiples(cypher, verbosity)

    if verbosity >= 2:
        print("Calculating distances between common ngrams...")
    distances = calc_distances(multiples, verbosity)
    dist_len = len(distances)
    del multiples

    if verbosity >= 2:
        print("Finding common divisors of distances...")
    div_freqs = find_common_divisors(distances, verbosity)
    del distances

    scores = {}  # dict of divisor to score
    for div, freq in div_freqs.items():
        weight = 50*math.log(0.1*freq+0.8)*(10/freq)
        scores[div] = freq*weight

    div_total = sum(div_freqs.values())
    top_div = max(div_freqs, key=(lambda k: scores[k]))
    confidence = div_freqs[top_div]/dist_len

    if verbosity >= 1:
        print(f"Found {len(div_freqs)} unique divisors for a total of {div_total}.\n"
              f"The Top Divisor is {top_div} that occurs {div_freqs[top_div]} times "
              f"({div_freqs[top_div]/div_total:.2%} of all divisors) within the cypher.\n"
              f"The Confidence level that this is the key length is {confidence:.2%}\n"
              f"A total of {dist_len} ngram pairs have been found."
              )
    if verbosity >= 2:
        print("All Divisors:")
        n = 1
        for key in sorted(div_freqs, key=lambda k: scores[k], reverse=True):
            value = div_freqs[key]

            print(f"#{n:3}: {value: 6}x {key: 6} ({value/div_total:.2%}) Score: {scores[key]: 8.2f}")

            n += 1

    key_length = top_div  # Just assume this, may not always work
    del div_freqs

    # Second Part of cracking algorithm
    # Uses Frequency Analysis to find the key

    raw_key = ""
    for i in range(key_length):
        sub_cypher = cypher[i::key_length]

        if verbosity >= 3:
            print(f"Subkey {i+1} Sub-Cypher: {sub_cypher}")

        most_common = collections.Counter(sub_cypher).most_common(2)

        if verbosity >= 2 and most_common[0][1] == most_common[1][1]:
            print(f"Ambiguous most common char for subkey #{i+1}, selecting a random one.")

        raw_key += most_common[0][0]

        if verbosity >= 3:
            print(f"Most common for subkey {i+1}: {most_common[0][0]} ({most_common[0][1]} times)"
                  f"Second Place: {most_common[1][0]} ({most_common[1][1]} times)")

    key = decrypt(raw_key, MOST_COMMON_LETTER*key_length)

    if verbosity >= 1:
        print(f"Found key '{key}'!")

    plain = decrypt(cypher, key)

    return plain, key


# Input Utility Function
def get_input(text_type: str) -> str:
    while True:
        choice = input(f"How do you want to supply the {text_type}? [F]ile | [C]lipboard | [D]irect Entry\n> ")

        if choice.lower() == "f":
            # Load from File
            fname = input("Please enter the path to the file here: ")

            if not os.path.exists(fname):
                print("Could not find a file with that name. Please try again.")
                continue
            elif not os.path.isfile(fname):
                print("The given path does not point to a file. Please try again.")
                continue

            print("Loading file...")
            with open(fname, "r") as f:
                data = f.read()

            data_len = len(data)
            data = normalize_text(data)

            print(f"Loaded File and removed {data_len-len(data)} characters of non-alphabetic characters.")

            return data
        elif choice.lower() == "c":
            if not HAVE_PYPERCLIP:
                print("pyperclip is required for accessing the clipboard.")
                continue

            data = pyperclip.paste()
            data_len = len(data)

            data = normalize_text(data)
            print(f"Successfully pasted {len(data)} characters of {data_len} raw characters.")

            return data

        elif choice.lower() == "d":
            print("Enter as many lines as you want."
                  "All text will be concatenated internally and non-alphabetic characters removed.\n"
                  "Data entry can be finished by pressing enter on an empty line.")

            data = ""
            while True:
                line = input()

                if line == "":
                    break

                data += line

            data_len = len(data)
            data = normalize_text(data)
            print(f"Data entry finished. Got {len(data)} characters of alphabetic text by throwing away"
                  f"{data_len-len(data)} characters.")

            return data
        else:
            print("Choice must be one of 'F', 'C' or 'D'.")


# Main Function
def main() -> None:
    global VERBOSITY

    print("Welcome to this Vigenere Cracker!\n"
          "This Cracker can quickly and reliably crack almost any long enough Vigenere-encrypted cyphertext.\n"
          "Type 'help' or 'h' for a short help page.")

    run = True
    while run:
        cmd = input("> ")

        if cmd in ["help", "h"]:
            # Help Command
            print("Quick Reference\n"
                  "Available Commands:\n"
                  "help     h       Print this Help page\n"
                  "encrypt  e       Encrypt some Plaintext using a key\n"
                  "decrypt  d       Decrypt some Cyphertext using a key\n"
                  "hide             Encrypt some Plaintext with a random key\n"
                  "crack    c       Decrypt some Cyphertext without a key\n"
                  "verbose  v       Increase the Verbosity of outputs\n"
                  "silent   s       Decrease the Verbosity of outputs\n"
                  "quit     q       Exits the Vigenere Cracker")
        elif cmd in ["encrypt", "e"]:
            # Encrypt Command
            plain = get_input("Plaintext")
            key = get_input("Key")

            st = time.time()
            cypher = encrypt(plain, key)
            et = time.time()

            print(f"Successfully encrypted {len(plain)} characters in {(et-st)*1000:.2f}ms")
            print("Cypher text:")
            print(cypher)
            print("End of cyphertext")

            if HAVE_PYPERCLIP and input("Do you want to copy the result to the clipboard? [Y/N] ").lower() == "y":
                    pyperclip.copy(cypher)
                    print("Successfully copied cyphertext to the clipboard!")
        elif cmd in ["decrypt", "d"]:
            # Decrypt Command
            cypher = get_input("Cyphertext")
            key = get_input("Key")

            st = time.time()
            plain = decrypt(cypher, key)
            et = time.time()

            print(f"Successfully decrypted {len(plain)} characters in {(et-st)*1000:.2f}ms")
            print("Plain text:")
            print(plain)
            print("End of plaintext")

            if HAVE_PYPERCLIP and input("Do you want to copy the result to the clipboard? [Y/N] ").lower() == "y":
                pyperclip.copy(plain)
                print("Successfully copied plaintext to the clipboard!")
        elif cmd in ["hide"]:
            print("This feature is not yet implemented.")
        elif cmd in ["crack", "c"]:
            # Crack Command
            cypher = get_input("Cyphertext")

            if len(cypher) > 2**16:
                print("It seems that the text you entered is quite long, "
                      "so please be patient while the algorithm does its work.\n"
                      "It is also recommended that you keep an eye on your memory usage while"
                      "the ngram analysis is running, as it may consume large amounts of memory.")

            st = time.time()
            plain, key = crack(cypher, VERBOSITY)
            et = time.time()

            print(f"Successfully cracked the cypher in {(et-st)*1000:.2f}ms")
            print("Plain Text:")
            print(plain)
            print("Key:")
            print(key)

            if HAVE_PYPERCLIP and input("Do you want to copy the result to the clipboard? [Y/N] ").lower() == "y":
                pyperclip.copy(plain)
                print("Successfully copied plaintext to the clipboard!")
        elif cmd in ["verbose", "v"]:
            VERBOSITY += 1
            print(f"Increased the verbosity to {VERBOSITY}.")
        elif cmd in ["silent", "s"]:
            VERBOSITY = max(0, VERBOSITY-1)
            print(f"Decreased the verbosity to {VERBOSITY}.")
        elif cmd in ["quit", "q"]:
            run = False
        else:
            print("Unknown command, please try again.")


if __name__ == "__main__":
    main()
