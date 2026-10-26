"""Second-route symbolic check of the non-V example, without geometry imports."""
from sympy import Matrix, Poly, expand, symbols


def main():
    h1, h2, h3, h4, h5, h6 = symbols('h1:7')
    # Jacobi--Trudi for (4,4,2)/(2,0,0); no diagram utility supplies this matrix.
    P = expand(Matrix([[h2, h5, h6], [h1, h4, h5], [0, h1, h2]]).det())
    quotient = Poly(P, h6).coeff_monomial(h6)  # three rows: positive corner sign
    assert quotient == h1**2
    # The middle cells (-2,2), (-1,1), (-1,2), (0,1) have no southeast pairs.
    O = {(-2, 2), (-1, 1), (-1, 2), (0, 1)}
    assert all((i+1, j+1) not in O for i, j in O)
    C = 1
    Theta = expand(quotient/C)
    assert Theta == h1**2
    assert max(int(str(x)[1:]) for x in Theta.free_symbols) == 1 <= 2
    assert Poly(P, h5).coeff_monomial(h5) != Theta  # wrong-coefficient control
    print('s_E =', P)
    print('kappa(s_E)/C =', Theta, '; span 1 <= width 2; control fired')
    print('check_witness_determinant: PASS')


if __name__ == '__main__':
    main()
