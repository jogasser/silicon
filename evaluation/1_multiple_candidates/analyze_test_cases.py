#!/usr/bin/env python3
import os
import re
from collections import defaultdict
import pandas as pd

def get_test_case_base_name(filename):
    """Extract base test case name from .smt2 filename"""
    # Remove the -00, -01, etc. suffix and .smt2 extension
    match = re.match(r'(.+)_iter\d+\.log-\d+\.smt2$', filename)
    if match:
        return match.group(1) + '_iter1'
    return None

def has_unknown_result(filepath):
    """Check if a .smt2 file contains any 'unknown' results"""
    try:
        with open(filepath, 'r') as f:
            content = f.read()
            return '; unknown' in content
    except:
        return False

def analyze_candidates():
    logs_dir = 'logs'
    candidates = sorted([d for d in os.listdir(logs_dir) 
                        if os.path.isdir(os.path.join(logs_dir, d))])
    
    results = {}
    
    for candidate in candidates:
        candidate_dir = os.path.join(logs_dir, candidate)
        
        # Group files by test case base name
        test_cases = defaultdict(list)
        
        for filename in os.listdir(candidate_dir):
            if filename.endswith('.smt2'):
                base_name = get_test_case_base_name(filename)
                if base_name:
                    filepath = os.path.join(candidate_dir, filename)
                    test_cases[base_name].append(filepath)
        
        # Count test cases without unknown results
        total_test_cases = len(test_cases)
        cases_without_unknown = 0
        
        for base_name, files in test_cases.items():
            # Check if ANY file for this test case has unknown
            has_unknown = any(has_unknown_result(f) for f in files)
            if not has_unknown:
                cases_without_unknown += 1
        
        results[candidate] = {
            'total_test_cases': total_test_cases,
            'cases_without_unknown': cases_without_unknown,
            'cases_with_unknown': total_test_cases - cases_without_unknown,
            'percentage_without_unknown': (cases_without_unknown / total_test_cases * 100) if total_test_cases > 0 else 0
        }
        
        print(f"Processed {candidate}: {cases_without_unknown}/{total_test_cases} cases without unknown")
    
    return results

if __name__ == '__main__':
    print("Analyzing test cases for unknown results...\n")
    results = analyze_candidates()
    
    # Create DataFrame and save
    df = pd.DataFrame.from_dict(results, orient='index')
    df = df.sort_values('cases_without_unknown', ascending=False)
    df.to_csv('test_cases_analysis.csv')
    
    print("\n" + "=" * 80)
    print(f"{'Candidate':<20} {'Total Cases':>12} {'Without Unknown':>16} {'With Unknown':>14} {'% Without':>12}")
    print("=" * 80)
    
    for candidate, data in df.iterrows():
        print(f"{candidate:<20} {int(data['total_test_cases']):>12} "
              f"{int(data['cases_without_unknown']):>16} "
              f"{int(data['cases_with_unknown']):>14} "
              f"{data['percentage_without_unknown']:>11.1f}%")
    
    print("\nResults saved to 'test_cases_analysis.csv'")
