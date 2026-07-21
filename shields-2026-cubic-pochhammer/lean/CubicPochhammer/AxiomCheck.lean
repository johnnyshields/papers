import CubicPochhammer
namespace CubicPochhammer
-- Deep combinatorial core: must be pure (no project axioms)
#print axioms Snj_nonneg
#print axioms three_R_closed
#print axioms sum_weighted_nonneg
-- Certificate: uses only Jm_bernstein
#print axioms Jm_pos
-- Kernel: uses Jm_bernstein + block_certificate
#print axioms Jmw_nonneg
-- Main theorem: full bridge set
#print axioms turan_coeff_nonneg
end CubicPochhammer
