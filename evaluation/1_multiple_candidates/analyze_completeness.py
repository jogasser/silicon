#!/usr/bin/env python3
"""
Analyze completeness of verification candidates compared to silicon baseline.
"""

import pandas as pd
from collections import defaultdict

def load_data(csv_path):
    """Load the times CSV file."""
    return pd.read_csv(csv_path)

def analyze_completeness(df):
    """
    Compare each candidate against silicon to find improvements and regressions.

    Returns a dictionary with results for each candidate.
    """
    # Get silicon results as baseline
    silicon_df = df[df['candidate'] == 'silicon'][['file', 'result']].copy()
    silicon_df.columns = ['file', 'silicon_result']

    # Get all candidates except silicon
    candidates = df[df['candidate'] != 'silicon']['candidate'].unique()

    results = {}

    for candidate in sorted(candidates):
        candidate_df = df[df['candidate'] == candidate][['file', 'result']].copy()
        candidate_df.columns = ['file', 'candidate_result']

        # Merge with silicon results
        comparison = pd.merge(silicon_df, candidate_df, on='file', how='inner')

        # Find improvements (silicon failed/timed out -> candidate succeeded)
        improvements = comparison[
            ((comparison['silicon_result'].isin(['failure', 'timeout'])) &
            (comparison['candidate_result'] == 'success')) |
            ((comparison['silicon_result'] == 'timeout') &
            (comparison['candidate_result'] != 'timeout'))
        ]

        # Find regressions (silicon succeeded -> candidate failed/timed out)
        regressions = comparison[
            ((comparison['silicon_result'] == 'success') &
            (comparison['candidate_result'].isin(['failure']))) 
        ]

        # Find changes between failure types
        success = comparison[(comparison['candidate_result'] == comparison['silicon_result']) & (comparison['silicon_result'] != 'timeout')]


        # Find changes between failure types
        timeouts = comparison[(comparison['candidate_result'] == 'timeout') & (comparison['silicon_result'] != 'timeout')]


        results[candidate] = {
            'success': success['file'].tolist(),
            'improvements': improvements['file'].tolist(),
            'regressions': regressions['file'].tolist(),
            'timeout': timeouts['file'].tolist(),
            'total_files': len(comparison)
        }

    return results

def print_summary(results):
    """Print a summary table of all candidates."""
    print("\n" + "="*100)
    print("COMPLETENESS COMPARISON SUMMARY (vs Silicon Baseline)")
    print("="*100)
    print(f"{'Candidate':<20} {'Improvements':<15} {'Regressions':<15} {'F→T':<10} {'T→F':<10}")
    print("-"*100)

    for candidate in sorted(results.keys()):
        r = results[candidate]
        print(f"{candidate:<20} "
              f"{len(r['improvements']):<15} "
              f"{len(r['regressions']):<15} "
              f"{len(r['timeout']):<10}")

    print("-"*100)
    print("Legend: F→T = Failure changed to Timeout, T→F = Timeout changed to Failure")
    print("="*100)

def print_detailed_results(results):
    """Print detailed results for each candidate."""
    print("\n\n" + "="*100)
    print("DETAILED RESULTS BY CANDIDATE")
    print("="*100)

    for candidate in sorted(results.keys()):
        r = results[candidate]
        print(f"\n{'='*100}")
        print(f"CANDIDATE: {candidate}")
        print(f"{'='*100}")

        if r['improvements']:
            print(f"\n✓ IMPROVEMENTS ({len(r['improvements'])}): Silicon failed/timeout → {candidate} success")
            print("-"*100)
            for file in sorted(r['improvements']):
                print(f"  + {file}")
        else:
            print(f"\n✓ IMPROVEMENTS: None")

        if r['regressions']:
            print(f"\n✗ REGRESSIONS ({len(r['regressions'])}): Silicon success → {candidate} failure/timeout")
            print("-"*100)
            for file in sorted(r['regressions']):
                print(f"  - {file}")
        else:
            print(f"\n✗ REGRESSIONS: None")

        if r['timeout']:
            print(f"\n⧗ TIMEOUT → FAILURE ({len(r['timeout'])})")
            print("-"*100)
            for file in sorted(r['timeout']):
                print(f"    {file}")

        # Net improvement calculation
        net = len(r['improvements']) - len(r['regressions']) - len(r['timeout'])
        print(f"\nNET CHANGE: {net:+d} (improvements - regressions)")

def main():
    csv_path = 'times.csv'

    print("Loading data from times.csv...")
    df = load_data(csv_path)

    print(f"Loaded {len(df)} records")
    print(f"Found {len(df['candidate'].unique())} candidates")
    print(f"Found {len(df['file'].unique())} unique files")

    print("\nAnalyzing completeness compared to silicon baseline...")
    results = analyze_completeness(df)

    print_summary(results)
    print_detailed_results(results)

    # Export to CSV
    export_data = []
    for candidate, r in results.items():
        export_data.append({
            'candidate': candidate,
            'success': len(r['success']),
            'timeout': len(r['timeout']),
            'regressions': len(r['regressions']),
            'improvements': len(r['improvements']),
        })

    export_df = pd.DataFrame(export_data)
    export_df = export_df.sort_values('success', ascending=False)
    export_df.to_csv('completeness_summary.csv', index=False)
    print(f"\n\nSummary exported to: completeness_summary.csv")

if __name__ == '__main__':
    main()
