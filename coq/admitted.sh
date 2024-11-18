#!/bin/bash

# Directory to search, fixed to "common"
SEARCH_DIR="common"

# Find all .v files in the "common" directory and search for "Admitted." and "Abort."
echo "Searching for 'Admitted.'..."
grep -rnw "$SEARCH_DIR" -e "Admitted."

if [ $? -ne 0 ]; then
    echo "No unfinished proofs (Admitted.) found in '$SEARCH_DIR'."
fi

echo "Searching for 'Abort.'..."
grep -rnw "$SEARCH_DIR" -e "Abort."

if [ $? -ne 0 ]; then
    echo "No proofs ending in Abort. found in '$SEARCH_DIR'."
fi
