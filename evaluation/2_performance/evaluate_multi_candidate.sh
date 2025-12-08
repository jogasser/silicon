#!/bin/bash
source "$HOME/.sdkman/bin/sdkman-init.sh"

sdk use java 11.0.27.fx-zulu

# Source candidate configurations
SOURCE_DIR="$(dirname "$0")"
source "${SOURCE_DIR}/candidate_configs.sh"

# Create base directories
mkdir -p output_comparison
mkdir -p analysis

# Initialize times.csv
> times.csv
echo "candidate,file,iteration,time,result" >> times.csv

# Initialize summary log
> evaluation_summary.log
echo "Multi-Candidate Evaluation Report" >> evaluation_summary.log
echo "==================================" >> evaluation_summary.log
echo "Date: $(date)" >> evaluation_summary.log
echo "Candidates: ${#CANDIDATE_NAMES[@]}" >> evaluation_summary.log
echo "" >> evaluation_summary.log

# List all candidates
echo "Candidates being evaluated:" >> evaluation_summary.log
for candidate in "${CANDIDATE_NAMES[@]}"; do
    echo "  - $candidate" >> evaluation_summary.log
done
echo "" >> evaluation_summary.log

# Find all .vpr files
vpr_files=$(find . -name "*.vpr" -type f | sort)
total=$(echo "$vpr_files" | wc -l)

echo "Found $total .vpr files to test"
echo "Testing ${#CANDIDATE_NAMES[@]} candidates with 5 iterations each"
echo "Total runs: $((total * ${#CANDIDATE_NAMES[@]} * 5))"
echo "================================"

# Process each .vpr file
current=0
for vpr_file in $vpr_files; do
    current=$((current + 1))

    # Get the relative path without the leading ./
    rel_path="${vpr_file#./}"

    # Create a sanitized log file name
    log_name=$(echo "$rel_path" | sed 's/\//_/g' | sed 's/\.vpr$/.log/')

    echo "[$current/$total] Testing: $rel_path"

    # Test each candidate
    for candidate in "${CANDIDATE_NAMES[@]}"; do
        echo "  Candidate: $candidate"

        # Create candidate-specific directories
        mkdir -p "logs/${candidate}"
        mkdir -p "output_comparison/${candidate}"

        # Get candidate options
        options="${CANDIDATES[$candidate]}"

        # Run 5 iterations
        for iteration in {1..5}; do
            echo "    Iteration $iteration/5"

            # Define output paths
            log_file="logs/${candidate}/${log_name%.log}_iter${iteration}.log"
            output_file="output_comparison/${candidate}/$(echo "$rel_path" | sed 's/\//_/g' | sed "s/\.vpr$/_iter${iteration}.txt/")"

            # Run silicon with candidate configuration
            # Use original silicon for "silicon" candidate, modified silicon for others
            if [ "$candidate" = "silicon" ]; then
                /root/silicon_orig/silicon.sh $options --proverLogFile "$log_file" "$vpr_file" > "$output_file" 2>&1
            else
                /root/silicon/silicon.sh $options --proverLogFile "$log_file" "$vpr_file" > "$output_file" 2>&1
            fi
            exit_code=$?

            # Extract timing
            time_result=$(grep -oP 'Silicon (found|finished).*? in \K[0-9.]+(?=s)' "$output_file" || echo "N/A")

            # Parse verification result
            if grep -q "Silicon finished verification successfully" "$output_file" || grep -q "Silicon found no errors" "$output_file"; then
                verification_result="success"
            elif grep -q "Timeout occurred" "$output_file" || grep -q "timeout" "$output_file" || [ "$exit_code" -eq 124 ]; then
                verification_result="timeout"
            else
                verification_result="failure"
            fi

            # Write to CSV
            echo "$candidate,$rel_path,$iteration,$time_result,$verification_result" >> times.csv
        done
    done

    echo ""
done

echo "================================"
echo "Evaluation complete!"
echo ""
echo "Results stored in:"
echo "  - times.csv (all timing data)"
echo "  - logs/<candidate>/ (prover logs per candidate)"
echo "  - output_comparison/<candidate>/ (outputs per candidate)"
echo "  - evaluation_summary.log (summary report)"
echo ""
echo "To analyze results, run: ./analyze_results.sh"
