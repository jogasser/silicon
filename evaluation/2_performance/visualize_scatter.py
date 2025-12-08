#!/usr/bin/env python3
"""
Performance Visualization - Scatter Plot Focus
Creates a scatter plot comparing runtimes and generates LaTeX table for outliers
"""

import pandas as pd
import matplotlib.pyplot as plt
import seaborn as sns
import numpy as np

# Set style
sns.set_style("whitegrid")
plt.rcParams['figure.dpi'] = 100
plt.rcParams['font.size'] = 14
plt.rcParams['axes.labelsize'] = 18
plt.rcParams['axes.titlesize'] = 20
plt.rcParams['xtick.labelsize'] = 14
plt.rcParams['ytick.labelsize'] = 14
plt.rcParams['legend.fontsize'] = 16
plt.rcParams['legend.title_fontsize'] = 16

# Read the data
print("Loading data from times.csv...")
df = pd.read_csv('times.csv')

# Calculate average runtime per test case per candidate
print("Calculating averages...")
avg_times = df.groupby(['candidate', 'file'])['time'].mean().reset_index()
avg_times.columns = ['candidate', 'file', 'avg_time']

# Pivot to have candidates as columns
pivot_times = avg_times.pivot(index='file', columns='candidate', values='avg_time')
pivot_times = pivot_times.dropna()

# Extract candidates
candidates = pivot_times.columns.tolist()
x_col, y_col = 'em-fmf', 'silicon'

# Calculate differences
pivot_times['difference'] = pivot_times[x_col] - pivot_times[y_col]
pivot_times['percent_diff'] = ((pivot_times[x_col] - pivot_times[y_col]) / pivot_times[y_col] * 100)
pivot_times['abs_difference'] = pivot_times['difference'].abs()

# ============================================================================
# CREATE SCATTER PLOT
# ============================================================================
fig, ax = plt.subplots(figsize=(12, 10))

# Identify outliers where em-fmf is significantly slower
# Criteria: difference > 5 seconds OR percent difference > 50%
outliers = pivot_times[(pivot_times['difference'] > 5) | (pivot_times['percent_diff'] > 50)]
normal = pivot_times[(pivot_times['difference'] <= 5) & (pivot_times['percent_diff'] <= 50)]

print(f"\nFound {len(outliers)} outliers where em-fmf is significantly slower")

# Plot normal points
ax.scatter(normal[x_col], normal[y_col], alpha=0.6, s=80,
           edgecolors='black', linewidth=0.7, label='Normal cases', color='steelblue')

# Plot outliers in red
ax.scatter(outliers[x_col], outliers[y_col], alpha=0.8, s=120,
           edgecolors='darkred', linewidth=2, label='em-fmf significantly slower',
           color='red', marker='o')

# Add diagonal line (equal performance)
max_val = max(pivot_times[x_col].max(), pivot_times[y_col].max())
min_val = 0
ax.plot([min_val, max_val], [min_val, max_val], 'k--',
        label='Equal performance', linewidth=2.5, alpha=0.7)

# Formatting
ax.set_xlabel(f'{x_col} Average Runtime (s)', fontweight='bold')
ax.set_ylabel(f'{y_col} Average Runtime (s)', fontweight='bold')
ax.set_title('Performance Comparison: em-fmf vs silicon\n(Each point = average runtime for one test case)',
             fontweight='bold', pad=20)
ax.legend(loc='upper left', frameon=True, shadow=True)
ax.grid(True, alpha=0.3)

# Statistics (for terminal output only)
faster_count_emfmf = (pivot_times[x_col] < pivot_times[y_col]).sum()
faster_count_silicon = (pivot_times[y_col] < pivot_times[x_col]).sum()
equal_count = (pivot_times[x_col] == pivot_times[y_col]).sum()

plt.tight_layout()
plt.savefig('performance_scatter.png', dpi=200, bbox_inches='tight')
print("\nScatter plot saved as 'performance_scatter.png'")

# ============================================================================
# GENERATE LATEX TABLE FOR OUTLIERS
# ============================================================================
print("\n" + "="*80)
print("GENERATING LATEX TABLE FOR OUTLIERS")
print("="*80)

# Sort outliers by difference (largest first)
outliers_sorted = outliers.sort_values('difference', ascending=False)

# Create LaTeX table
latex_lines = []
latex_lines.append(r"\begin{table}[htbp]")
latex_lines.append(r"    \centering")
latex_lines.append(r"    \caption{Test cases where em-fmf is significantly slower than silicon}")
latex_lines.append(r"    \label{tab:performance_outliers}")
latex_lines.append(r"    \begin{tabular}{lrrrc}")
latex_lines.append(r"        \toprule")
latex_lines.append(r"        \textbf{Test Case} & \textbf{em-fmf (s)} & \textbf{silicon (s)} & \textbf{Difference (s)} & \textbf{Slowdown (\%)} \\")
latex_lines.append(r"        \midrule")

for test_file, row in outliers_sorted.iterrows():
    # Clean up file name - remove directory path and .vpr extension
    test_name = test_file.replace('/', r'/\allowbreak ').replace('_', r'\_')
    em_fmf_time = row[x_col]
    silicon_time = row[y_col]
    diff = row['difference']
    percent = row['percent_diff']

    latex_lines.append(f"        {test_name} & {em_fmf_time:.2f} & {silicon_time:.2f} & {diff:.2f} & {percent:.1f} \\\\")

latex_lines.append(r"        \bottomrule")
latex_lines.append(r"    \end{tabular}")
latex_lines.append(r"\end{table}")

# Join all lines
latex_table = '\n'.join(latex_lines)

# Save to file
with open('outliers_table.tex', 'w') as f:
    f.write(latex_table)

print("\nLaTeX table saved to 'outliers_table.tex'")
print("\nLaTeX table preview:")
print("="*80)
print(latex_table)
print("="*80)

# Also print a simple summary
print(f"\n\nOUTLIERS SUMMARY (em-fmf significantly slower):")
print("="*80)
print(f"{'Test Case':<45} {'em-fmf':>10} {'silicon':>10} {'Diff':>10} {'%':>10}")
print("-"*80)
for test_file, row in outliers_sorted.iterrows():
    test_name = test_file.split('/')[-1][:40]  # Just filename, truncated
    print(f"{test_name:<45} {row[x_col]:>10.2f} {row[y_col]:>10.2f} {row['difference']:>10.2f} {row['percent_diff']:>9.1f}%")

print("\n" + "="*80)
print(f"TOTAL OUTLIERS: {len(outliers_sorted)}")
print(f"Criteria: difference > 5s OR slowdown > 50%")
print("="*80)

print("\nVisualization complete!")
print("\nNote: To use the LaTeX table, make sure to include \\usepackage{booktabs} in your preamble")
