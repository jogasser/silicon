#!/usr/bin/env python3
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

# Read the CSV file
df = pd.read_csv('candidate_sat_stats.csv')

# Remove any empty rows
df = df.dropna()

# Set candidate as index
df = df.set_index('candidate')

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

# Create figure with single plot
fig, ax = plt.subplots(figsize=(12, 10))

# Define colors for each result type
colors = {
    'sat': '#3498db',      # Blue
    'unsat': '#27ae60',    # Green
    'unknown': '#e74c3c'   # Red
}

# Stacked bar chart showing distribution
candidates = df.index
x_pos = np.arange(len(candidates))

ax.barh(x_pos, df['sat'], label='SAT', color=colors['sat'])
ax.barh(x_pos, df['unsat'], left=df['sat'], label='UNSAT', color=colors['unsat'])
ax.barh(x_pos, df['unknown'], left=df['sat'] + df['unsat'], label='Unknown', color=colors['unknown'])

ax.set_yticks(x_pos)
ax.set_yticklabels(candidates, fontsize=14)
ax.set_xlabel('Number of Results', fontsize=16, fontweight='bold')
ax.set_title('SAT Solver Results by Candidate', fontsize=18, fontweight='bold')
ax.tick_params(axis='x', labelsize=14)
ax.legend(loc='lower right', fontsize=14)
ax.grid(axis='x', alpha=0.3)

plt.tight_layout()
plt.savefig('candidate_sat_stats.png', dpi=300, bbox_inches='tight')
print("Graph saved as 'candidate_sat_stats.png'")

# Print summary statistics
print("\nSummary Statistics:")
print("=" * 60)
print(f"{'Candidate':<20} {'Total':>10} {'Unknown %':>12} {'SAT %':>10} {'UNSAT %':>10}")
print("=" * 60)
for candidate in custom_order:
    row = df.loc[candidate]
    total = row['sat'] + row['unsat'] + row['unknown']
    unk_pct = row['unknown'] / total * 100
    sat_pct = row['sat'] / total * 100
    unsat_pct = row['unsat'] / total * 100
    print(f"{candidate:<20} {int(total):>10} {unk_pct:>11.1f}% {sat_pct:>9.1f}% {unsat_pct:>9.1f}%")
