import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

# Read the data
df = pd.read_csv('completeness_summary.csv')

# Sort by net_change (descending, so best candidates first)
df = df.sort_values('net_change', ascending=False)

# Create figure with subplots
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 8))

# Plot 1: Improvements vs Regressions
x = np.arange(len(df))
width = 0.35

bars1 = ax1.barh(x - width/2, df['improvements'], width, label='Improvements', color='#2ecc71', alpha=0.8)
bars2 = ax1.barh(x + width/2, -df['regressions'], width, label='Regressions', color='#e74c3c', alpha=0.8)

ax1.set_yticks(x)
ax1.set_yticklabels(df['candidate'], fontsize=9)
ax1.set_xlabel('Count', fontsize=11)
ax1.set_title('Improvements vs Regressions by Candidate', fontsize=13, fontweight='bold')
ax1.legend(loc='lower right')
ax1.axvline(x=0, color='black', linewidth=0.8)
ax1.grid(axis='x', alpha=0.3)

# Add value labels on bars
for bar in bars1:
    width_val = bar.get_width()
    if width_val > 0:
        ax1.text(width_val, bar.get_y() + bar.get_height()/2, f'{int(width_val)}',
                ha='left', va='center', fontsize=8, color='darkgreen', fontweight='bold')

for bar in bars2:
    width_val = bar.get_width()
    if width_val < 0:
        ax1.text(width_val, bar.get_y() + bar.get_height()/2, f'{int(-width_val)}',
                ha='right', va='center', fontsize=8, color='darkred', fontweight='bold')

# Plot 2: Net Change
colors = ['#2ecc71' if val > -10 else '#e67e22' if val > -20 else '#e74c3c' for val in df['net_change']]
bars = ax2.barh(x, df['net_change'], color=colors, alpha=0.8)

ax2.set_yticks(x)
ax2.set_yticklabels(df['candidate'], fontsize=9)
ax2.set_xlabel('Net Change', fontsize=11)
ax2.set_title('Net Change by Candidate (Improvements - Regressions)', fontsize=13, fontweight='bold')
ax2.axvline(x=0, color='black', linewidth=0.8)
ax2.grid(axis='x', alpha=0.3)

# Add value labels on bars
for bar in bars:
    width_val = bar.get_width()
    label_x = width_val - 0.5 if width_val < -5 else width_val + 0.5
    ha = 'right' if width_val < -5 else 'left'
    ax2.text(label_x, bar.get_y() + bar.get_height()/2, f'{int(width_val)}',
            ha=ha, va='center', fontsize=8, fontweight='bold')

plt.tight_layout()
plt.savefig('completeness_comparison.png', dpi=300, bbox_inches='tight')
print("Plot saved as 'completeness_comparison.png'")

# Also create a detailed comparison plot
fig2, ((ax3, ax4), (ax5, ax6)) = plt.subplots(2, 2, figsize=(16, 12))

# Subplot 1: Stacked bar for all metrics
metrics = ['improvements', 'failure_to_timeout', 'timeout_to_failure']
negative_metrics = ['regressions']

x_pos = np.arange(len(df))

# Positive contributions
bottom = np.zeros(len(df))
colors_pos = ['#2ecc71', '#3498db', '#9b59b6']
for i, metric in enumerate(metrics):
    ax3.barh(x_pos, df[metric], left=bottom, label=metric.replace('_', ' ').title(),
             color=colors_pos[i], alpha=0.8)
    bottom += df[metric].values

# Negative contributions
ax3.barh(x_pos, -df['regressions'], label='Regressions', color='#e74c3c', alpha=0.8)

ax3.set_yticks(x_pos)
ax3.set_yticklabels(df['candidate'], fontsize=9)
ax3.set_xlabel('Count', fontsize=11)
ax3.set_title('Detailed Breakdown by Candidate', fontsize=13, fontweight='bold')
ax3.legend(loc='lower right', fontsize=9)
ax3.axvline(x=0, color='black', linewidth=0.8)
ax3.grid(axis='x', alpha=0.3)

# Subplot 2: Net change with color gradient
net_changes = df['net_change'].values
colors_gradient = plt.cm.RdYlGn([(val + 27) / 19 for val in net_changes])  # Normalize to [0,1]
bars = ax4.barh(x_pos, net_changes, color=colors_gradient, alpha=0.9)

ax4.set_yticks(x_pos)
ax4.set_yticklabels(df['candidate'], fontsize=9)
ax4.set_xlabel('Net Change', fontsize=11)
ax4.set_title('Net Change (Color-coded)', fontsize=13, fontweight='bold')
ax4.axvline(x=0, color='black', linewidth=0.8)
ax4.grid(axis='x', alpha=0.3)

# Subplot 3: Scatter plot - Improvements vs Regressions
ax5.scatter(df['improvements'], df['regressions'], s=200, alpha=0.6, c=df['net_change'], cmap='RdYlGn')
for idx, row in df.iterrows():
    ax5.annotate(row['candidate'], (row['improvements'], row['regressions']),
                fontsize=7, alpha=0.7, ha='center')
ax5.set_xlabel('Improvements', fontsize=11)
ax5.set_ylabel('Regressions', fontsize=11)
ax5.set_title('Improvements vs Regressions Scatter', fontsize=13, fontweight='bold')
ax5.grid(alpha=0.3)

# Subplot 4: Summary statistics table
top_5 = df.head(5)[['candidate', 'improvements', 'regressions', 'net_change']]
table_data = []
for idx, row in top_5.iterrows():
    table_data.append([row['candidate'], int(row['improvements']),
                      int(row['regressions']), int(row['net_change'])])

ax6.axis('tight')
ax6.axis('off')
table = ax6.table(cellText=table_data,
                 colLabels=['Candidate', 'Improvements', 'Regressions', 'Net Change'],
                 cellLoc='center', loc='center', colWidths=[0.3, 0.2, 0.2, 0.2])
table.auto_set_font_size(False)
table.set_fontsize(10)
table.scale(1, 2)

# Style header
for i in range(4):
    table[(0, i)].set_facecolor('#3498db')
    table[(0, i)].set_text_props(weight='bold', color='white')

# Style rows
for i in range(1, len(table_data) + 1):
    for j in range(4):
        if i % 2 == 0:
            table[(i, j)].set_facecolor('#ecf0f1')

ax6.set_title('Top 5 Candidates', fontsize=13, fontweight='bold', pad=20)

plt.tight_layout()
plt.savefig('completeness_detailed.png', dpi=300, bbox_inches='tight')
print("Detailed plot saved as 'completeness_detailed.png'")

# Print summary statistics
print("\n=== Summary Statistics ===")
print(f"\nBest candidate: {df.iloc[0]['candidate']} (net change: {df.iloc[0]['net_change']})")
print(f"Worst candidate: {df.iloc[-1]['candidate']} (net change: {df.iloc[-1]['net_change']})")
print(f"\nAverage improvements: {df['improvements'].mean():.2f}")
print(f"Average regressions: {df['regressions'].mean():.2f}")
print(f"Average net change: {df['net_change'].mean():.2f}")
