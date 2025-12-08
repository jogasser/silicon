1. Configure candidates in `candidate_config.sh`
2. Run `evaluate_multi_candidate.sh`, the data is stored in times.csv. The SMT-LIB logs in ./logs,

3. Run auxiliary analyses:
   1. `analyze_candidates.py`
   2. `analyze_completeness.py`
   3. `analyze_test_cases.py`
   4. `analyze_timeouts.py`

4. Plot images:
   1. `plot_completeness.py`
   2. `plot_results.py`
   2. `plot_test_cases.py`