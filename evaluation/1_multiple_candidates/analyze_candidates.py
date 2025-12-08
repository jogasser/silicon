#!/usr/bin/env python3
"""
Analyze SAT solver statistics for each candidate in the logs subdirectories.
"""

import os
import re
from pathlib import Path
from collections import defaultdict

def analyze_log_file(filepath):
    """
    Analyze a single log file and count check-sat calls and results.
    Returns a dict with counts.
    """
    counts = {
        'check_sat': 0,
        'sat': 0,
        'unsat': 0,
        'unknown': 0
    }

    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()

        i = 0
        while i < len(lines):
            line = lines[i].strip()

            # Check if this is a check-sat call
            if line == '(check-sat)':
                counts['check_sat'] += 1

                # Look at the next line for the result
                if i + 1 < len(lines):
                    next_line = lines[i + 1].strip()

                    # Results are in comments
                    if next_line.startswith(';'):
                        result = next_line[1:].strip().lower()

                        if result == 'sat':
                            counts['sat'] += 1
                        elif result == 'unsat':
                            counts['unsat'] += 1
                        elif result == 'unknown':
                            counts['unknown'] += 1

            i += 1

    except Exception as e:
        print(f"Error reading {filepath}: {e}")

    return counts

def analyze_candidate(logs_dir, candidate_name):
    """
    Analyze all log files for a given candidate.
    """
    candidate_dir = os.path.join(logs_dir, candidate_name)

    if not os.path.isdir(candidate_dir):
        return None

    total_counts = {
        'check_sat': 0,
        'sat': 0,
        'unsat': 0,
        'unknown': 0
    }

    # Process all .smt2 files in the candidate directory
    for filename in os.listdir(candidate_dir):
        if filename.endswith('.smt2'):
            filepath = os.path.join(candidate_dir, filename)
            file_counts = analyze_log_file(filepath)

            for key in total_counts:
                total_counts[key] += file_counts[key]

    return total_counts

def main():
    logs_dir = './logs'

    if not os.path.exists(logs_dir):
        print(f"Error: {logs_dir} directory not found")
        return

    # Get all candidate directories
    candidates = sorted([d for d in os.listdir(logs_dir)
                        if os.path.isdir(os.path.join(logs_dir, d))])

    print("Analyzing candidates...")
    print("=" * 80)

    results = {}

    for candidate in candidates:
        print(f"Processing: {candidate}")
        counts = analyze_candidate(logs_dir, candidate)

        if counts:
            results[candidate] = counts

    print("\n" + "=" * 80)
    print("RESULTS")
    print("=" * 80)
    print()

    # Print header
    print(f"{'Candidate':<25} {'check-sat calls':>15} {'unknown':>10} {'sat':>10} {'unsat':>10}")
    print("-" * 80)

    # Print results for each candidate
    for candidate in sorted(results.keys()):
        counts = results[candidate]
        print(f"{candidate:<25} {counts['check_sat']:>15,} {counts['unknown']:>10,} "
              f"{counts['sat']:>10,} {counts['unsat']:>10,}")

    print("=" * 80)

    # Save to CSV
    csv_file = 'candidate_sat_stats.csv'
    with open(csv_file, 'w') as f:
        f.write('candidate,check_sat_calls,unknown,sat,unsat\n')
        for candidate in sorted(results.keys()):
            counts = results[candidate]
            f.write(f"{candidate},{counts['check_sat']},{counts['unknown']},"
                   f"{counts['sat']},{counts['unsat']}\n")

    print(f"\nResults saved to: {csv_file}")

if __name__ == '__main__':
    main()
