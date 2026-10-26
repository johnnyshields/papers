#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
for script in \
    verify_charts.py \
    check_landing_data_satisfiable.py \
    check_source_chart_support.py \
    check_mixed_baseline_det.py \
    check_row_mark_mixed_words.py \
    check_mixed_one_period_coframe.py \
    check_mixed_coframe_legal_marks.py \
    check_low_row_response.py \
    check_neutral_returns.py \
    check_coarse_adjugate_weight.py \
    check_live_crossing.py \
    verify_transports.py \
    verify_rectangle_words.py \
    verify_empty_cycles.py \
    check_two_copy_flags.py \
    verify_rectangular_splice.py \
    check_first_grade.py \
    check_core_facts.py \
    check_all_j.py \
    check_mark_child_equality.py \
    check_mixed_normalization.py \
    check_ordinary_high_square.py \
    check_mixed_low_row_cofactor.py \
    verify_pinches.py \
    verify_endpoint_splice.py \
    verify_endpoint_product.py \
    verify_signed_cap.py \
    verify_wide_upper.py \
    verify_literal_mixed.py \
    verify_aligned_finish.py \
    verify_upper_mate.py \
    verify_mixed_upper_sign.py \
    verify_two_window.py \
    verify_reflection.py \
    verify_structured_dual.py \
    verify_principal_star.py \
    verify_zero_matrix.py \
    verify_signed_windows.py \
    verify_endpoint_consumer.py \
    verify_terminal_signed.py \
    check_domino_probe.py \
    check_preprocessing_scores.py \
    check_ordinary_amplified.py \
    check_high_head.py \
    check_line_finer.py \
    check_coframes.py \
    check_two_copy_equation.py \
    check_transpose.py \
    check_ordinary_zero.py \
    check_self_inner.py \
    check_mixed_empty.py \
    check_first_matrix.py \
    verify_mark_determinants.py
do
    echo "== $script"
    python3 "$script"
done
printf 'ALL PASS\n'
