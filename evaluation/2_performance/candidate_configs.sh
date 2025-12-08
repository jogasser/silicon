#!/bin/bash


# Base options that all candidates share
BASE_OPTS="--cvc5Exe /root/cvc5-Linux-x86_64-static/bin/cvc5 --numberOfParallelVerifiers 1 --timeout 100 --proverEnableResourceBounds --proverResourcesPerMillisecond 200"

declare -A CANDIDATES

# Original Silicon (no special args, just base options)
CANDIDATES["silicon"]="--z3Exe /root/z3-4.8.7-x64-ubuntu-16.04/bin/z3 --numberOfParallelVerifiers 1  --timeout 100 --proverEnableResourceBounds --proverResourcesPerMillisecond 1600"


CANDIDATES["em-fmf"]="$BASE_OPTS --cvc5EMatching true --cvc5FiniteModelFind true " 
#CANDIDATES["em-fmf-fun"]="$BASE_OPTS --cvc5EMatching true --cvc5FiniteModelFind true --cvc5FmfFunRlv true" 

# Export candidate names for iteration
export CANDIDATE_NAMES=($(echo "${!CANDIDATES[@]}" | tr ' ' '\n' | sort))

# Function to get options for a candidate
get_candidate_options() {
    local candidate=$1
    echo "${CANDIDATES[$candidate]}"
}

# Export the function
export -f get_candidate_options

# Print configuration summary
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    echo "=== CVC5 Candidate Configurations ==="
    echo "Total candidates: ${#CANDIDATES[@]}"
    echo ""
    echo "Candidates:"
    for candidate in $(echo "${!CANDIDATES[@]}" | tr ' ' '\n' | sort); do
        echo "  $candidate"
    done
fi

