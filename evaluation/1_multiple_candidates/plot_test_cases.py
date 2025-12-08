#!/usr/bin/env python3
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

# Read the CSV file
df = pd.read_csv('test_cases_analysis.csv', index_col=0)

# Define custom order (mapping user labels to actual CSV labels)
custom_order = [
    'silicon',
    'all',          # all-on
    'no-em',        # no-ematching
    'cbqi-cegqi',
    'mbqi-cegqi',
    'mbqi-cbqi',
    'fmf-fun-cegqi',
    'fmf-fun-cbqi',
    'fmf-fun-mbqi',
    'fmf-cebqi',    # fmf-cegqi (note: typo in CSV)
    'fmf-cbqi',
    'fmf-mbqi',
    'em-mbqi',
    'em-fmf-fun',
    'em-fmf',
    'em-cegqi',
    'em-cbqi',
    'fmf-fun',
    'fmf',
    'cegqi',
    'mbqi',
    'cbqi',
    'em',
    'no-qi'         # no-heuristics
]

# Filter to only include candidates that exist in the dataframe
custom_order = [c for c in custom_order if c in df.index]

# Reorder dataframe
df = df.loc[custom_order]

# Create figure
fig, ax = plt.subplots(figsize=(12, 10))

# Define colors
colors = {
    'without_unknown': '#27ae60',  # Green - successful
    'with_unknown': '#e74c3c'      # Red - problematic
}

# Stacked bar chart
candidates = df.index
x_pos = np.arange(len(candidates))

ax.barh(x_pos, df['cases_without_unknown'], label='Without Unknown', color=colors['without_unknown'])
ax.barh(x_pos, df['cases_with_unknown'], left=df['cases_without_unknown'], 
        label='With Unknown', color=colors['with_unknown'])

ax.set_yticks(x_pos)
ax.set_yticklabels(candidates, fontsize=14)
ax.set_xlabel('Number of Test Cases', fontsize=16, fontweight='bold')
ax.set_title('Test Cases Solved Without Unknown Results', fontsize=18, fontweight='bold')
ax.tick_params(axis='x', labelsize=14)
ax.legend(loc='lower right', fontsize=14)
ax.grid(axis='x', alpha=0.3)

# Add total reference line
total_cases = df['total_test_cases'].iloc[0]
ax.axvline(x=total_cases, color='gray', linestyle='--', linewidth=1, alpha=0.5)

plt.tight_layout()
plt.savefig('test_cases_analysis.png', dpi=300, bbox_inches='tight')
print("Graph saved as 'test_cases_analysis.png'")

# Print summary
print("\nSummary:")
print("=" * 70)
print(f"{'Candidate':<20} {'Without Unknown':>17} {'With Unknown':>15} {'% Success':>12}")
print("=" * 70)
for candidate in custom_order:
    row = df.loc[candidate]
    print(f"{candidate:<20} {int(row['cases_without_unknown']):>17} "
          f"{int(row['cases_with_unknown']):>15} "
          f"{row['percentage_without_unknown']:>11.1f}%")
