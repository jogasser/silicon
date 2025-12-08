#!/usr/bin/env python3
"""
Analyzes CSV file to count timeout results per file and identify which candidates did not timeout.
"""

import csv
import sys
from collections import defaultdict
from pathlib import Path


def analyze_timeouts(csv_path):
    """
    Analyzes timeout results from CSV file.
    Only counts candidates as successful if they match silicon's result and didn't timeout.

    Args:
        csv_path: Path to the CSV file with columns: candidate, file, iteration, time, result
    """
    # Data structures to track results
    timeout_counts = defaultdict(int)  # file -> count of timeouts
    # file -> candidate -> iteration -> result
    file_candidate_iteration_results = defaultdict(lambda: defaultdict(dict))

    # Read CSV file
    try:
        with open(csv_path, 'r') as f:
            reader = csv.DictReader(f)

            # Verify required columns exist
            required_cols = {'candidate', 'file', 'iteration', 'time', 'result'}
            if not required_cols.issubset(reader.fieldnames):
                print(f"Error: CSV must contain columns: {required_cols}")
                print(f"Found columns: {reader.fieldnames}")
                sys.exit(1)

            # Process each row
            for row in reader:
                file_name = row['file']
                candidate = row['candidate']
                iteration = row['iteration']
                result = row['result']

                # Track all results for each file-candidate-iteration combination
                file_candidate_iteration_results[file_name][candidate][iteration] = result

                # Count timeouts
                if result.lower() == 'timeout':
                    timeout_counts[file_name] += 1

    except FileNotFoundError:
        print(f"Error: File '{csv_path}' not found")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading CSV: {e}")
        sys.exit(1)

    # Get all files, not just ones with timeouts
    all_files = sorted(file_candidate_iteration_results.keys())

    # Sort files by timeout count (descending)
    sorted_files_with_timeouts = sorted(timeout_counts.items(), key=lambda x: x[1], reverse=True)

    # Report results
    print("=" * 80)
    print("TIMEOUT ANALYSIS REPORT")
    print("=" * 80)
    print()

    if timeout_counts:
        print(f"Total files with timeouts: {len(sorted_files_with_timeouts)}")
        print()

        print("Files ranked by number of timeouts:")
        print("-" * 80)
        for file_name, count in sorted_files_with_timeouts:
            print(f"{file_name}: {count} timeout(s)")
        print()
    else:
        print("No timeout results found in the CSV file.")
        print()

    # Show all candidates that matched silicon for ALL files
    print("=" * 80)
    print("CANDIDATES THAT MATCHED SILICON (all files)")
    print("=" * 80)
    print()

    for file_name in all_files:
        candidates_data = file_candidate_iteration_results[file_name]

        # Get silicon's results for this file
        if 'silicon' not in candidates_data:
            print(f"\n{file_name}:")
            print("-" * 80)
            print("  WARNING: No 'silicon' candidate found for this file")
            continue

        silicon_results = candidates_data['silicon']

        # Compare each candidate to silicon
        matching_candidates = []
        partial_match_candidates = []

        for candidate, iterations in candidates_data.items():
            if candidate == 'silicon':
                continue

            matched_count = 0
            total_count = 0
            timeout_count_candidate = 0

            for iteration, result in iterations.items():
                if iteration in silicon_results:
                    total_count += 1
                    silicon_result = silicon_results[iteration]

                    if result.lower() == 'timeout':
                        timeout_count_candidate += 1
                    elif result == silicon_result:
                        matched_count += 1

            if total_count > 0:
                if matched_count == total_count:
                    matching_candidates.append(candidate)
                elif matched_count > 0 or timeout_count_candidate > 0:
                    partial_match_candidates.append(
                        (candidate, matched_count, timeout_count_candidate, total_count)
                    )

        # Get timeout count for this file
        timeout_count = timeout_counts.get(file_name, 0)

        print(f"\n{file_name} ({timeout_count} timeout(s) total):")
        print("-" * 80)

        # Check if silicon itself had timeouts
        silicon_timeouts = sum(1 for r in silicon_results.values() if r.lower() == 'timeout')
        if silicon_timeouts > 0:
            print(f"  NOTE: Silicon itself had {silicon_timeouts} timeout(s)")

        if matching_candidates:
            print(f"  Candidates matching silicon on ALL iterations: {', '.join(sorted(matching_candidates))}")
        else:
            print("  No candidates matched silicon on all iterations")

        if partial_match_candidates:
            print(f"  Candidates with partial matches:")
            for cand, match_cnt, timeout_cnt, total in sorted(partial_match_candidates):
                mismatch_cnt = total - match_cnt - timeout_cnt
                print(f"    - {cand}: {match_cnt}/{total} matched, "
                      f"{timeout_cnt} timeout(s), {mismatch_cnt} mismatched")

    print()

    # Additional section for files with timeouts (for quick reference)
    if timeout_counts:
        print("=" * 80)
        print("SUMMARY: FILES WITH TIMEOUTS")
        print("=" * 80)
        print()

        for file_name, timeout_count in sorted_files_with_timeouts:
            candidates_data = file_candidate_iteration_results[file_name]

            # Get silicon's results for this file
            if 'silicon' not in candidates_data:
                print(f"\n{file_name} ({timeout_count} timeout(s) total):")
                print("-" * 80)
                print("  WARNING: No 'silicon' candidate found for this file")
                continue

            silicon_results = candidates_data['silicon']

            # Compare each candidate to silicon
            matching_candidates = []
            partial_match_candidates = []

            for candidate, iterations in candidates_data.items():
                if candidate == 'silicon':
                    continue

                matched_count = 0
                total_count = 0
                timeout_count_candidate = 0

                for iteration, result in iterations.items():
                    if iteration in silicon_results:
                        total_count += 1
                        silicon_result = silicon_results[iteration]

                        if result.lower() == 'timeout':
                            timeout_count_candidate += 1
                        elif result == silicon_result:
                            matched_count += 1

                if total_count > 0:
                    if matched_count == total_count:
                        matching_candidates.append(candidate)
                    elif matched_count > 0 or timeout_count_candidate > 0:
                        partial_match_candidates.append(
                            (candidate, matched_count, timeout_count_candidate, total_count)
                        )

            print(f"\n{file_name} ({timeout_count} timeout(s) total):")
            print("-" * 80)

            # Check if silicon itself had timeouts
            silicon_timeouts = sum(1 for r in silicon_results.values() if r.lower() == 'timeout')
            if silicon_timeouts > 0:
                print(f"  NOTE: Silicon itself had {silicon_timeouts} timeout(s)")

            if matching_candidates:
                print(f"  Candidates matching silicon on ALL iterations: {', '.join(sorted(matching_candidates))}")
            else:
                print("  No candidates matched silicon on all iterations")

            if partial_match_candidates:
                print(f"  Candidates with partial matches:")
                for cand, match_cnt, timeout_cnt, total in sorted(partial_match_candidates):
                    mismatch_cnt = total - match_cnt - timeout_cnt
                    print(f"    - {cand}: {match_cnt}/{total} matched, "
                          f"{timeout_cnt} timeout(s), {mismatch_cnt} mismatched")

    print()


def main():
    if len(sys.argv) != 2:
        print("Usage: python analyze_timeouts.py <csv_file>")
        print()
        print("Analyzes timeout results from a CSV file with columns:")
        print("  candidate, file, iteration, time, result")
        sys.exit(1)

    csv_path = sys.argv[1]
    analyze_timeouts(csv_path)


if __name__ == '__main__':
    main()

