#Section 2.2: computes period of an irreducible polynomial over a prime field
def period0(pol):
    F = pol.base_ring()
    assert F.is_prime_field()
    assert pol.is_irreducible()

    R = pol.parent()
    K.<y> = QuotientRing(R,R.ideal(pol))
    q = F.characteristic()^pol.degree() - 1
    for p in prime_factors(q):
        while (q%p==0) and (y^(q//p)==1):
            q //= p
    return q

#Section 2.2: computes period of any polynomial over a prime field
def period1(pol):
    F = pol.base_ring()
    assert F.is_prime_field()
    p = F.characteristic()
    pol >>= pol.ord()
    f = factor(pol)
    c = (max(d for _,d in f) - 1).ndigits(p)
    return lcm( period0(g) for g,_ in f ) * p^c

#Section 2.2: computes defect and period of polynomial x^2 - a*x - b modulo prime power q
def defect_period(a,b,q):
    p,_ = is_prime_power(q, get_data=True)
    R.<x> = PolynomialRing(Zmod(q))
    pol = x^2 - a*x - b

    t = period1(pol.change_ring(GF(p)))

    # lifing t to modulo p^m
    K.<y> = QuotientRing(R,[pol >> pol.ord()])
    while y^t != 1:
        t *= p
    return (pol.ord(), t)

#Section 2.2: computes the period of recurrent sequence $x_{k+1}=a*x_{k} + b*x_{k-1}$ with initial values $x_0$ and $x_1$ modulo q
def findij(x0,x1,a,b,q):
    d,t = defect_period(a,b,q)
    M = Matrix(Zmod(q),[[0,1],[b,a]])
    x = vector(Zmod(q),[x0,x1])

    # try to reduce t if possible
    for p in prime_factors(t):
        while (t%p==0) and M^(t//p + d)*x == M^d*x:
            t //= p

    # try to decrease d if possible
    while d>0 and M^(t//p + d-1)*x == M^(d-1)*x:
        d -= 1

    return (d,d+t)


#Section 3.2
def findzeros(x0,x1,a,b,q,i,j):
    #for $x_{k+1}=a*x_{k} + b*x_{k-1}$ with initial values $x_0$ and $x_1$
    #assume that there may be nonperiodic zeros between $x_0$ and $x_j$
    #compute terms that are congruent to zero modulo $p$ between $x_0$ and $x_j$
    K1 = []
    K2 = []
    u = Zmod(q)(x0)
    v = Zmod(q)(x1)
    for k in range(0,j):
        if u == 0:
            if k < i :
                K1.append(k)
            else:
                K2.append(k)
        u, v = v, a*v + b*u

    return [K1, K2]



# Solve Pell-Fermat equation C*x^2 - D*y^2 = N  (Section 2.3)
# Input: C, D, N
# Output: list of tuples of parameters (x0,x1,a,b), each defining a recurrence sequences giving solutins x
def pf_solve(C,D,N):
    K.<x> = QuadraticField(C*D)
    u = K.units()[0]
    if u.norm() == -1:
        u = u^2

    f = minpoly(u)
    a = -f[1]
    b = -f[0]
    r = []
    for s in K.elements_of_norm(C*N):
        x0 = lift(s)[0]/C
        x1 = lift(s*u)[0]/C
        if x1 < 0:
            x0,x1 = -x0,-x1
        if x0.is_integer() and x1.is_integer():
            r.append( (ZZ(x0),ZZ(x1),ZZ(a),ZZ(b)) )
        else:
            m = lcm(x0.denominator(), x1.denominator())
            ij = findij(x0*m, x1*m, a, b, m)
            per = ij[1] - ij[0]
            zer = findzeros(x0*m, x1*m, a,b, m, *ij)
            assert zer[0]==[]    # other case is impossible(?)

            for j in zer[1]:
                x0 = lift(s*u^j)[0]/C
                x1 = lift(s*u^(j+per))[0]/C
                if x1 < 0:
                    x0,x1 = -x0,-x1
                ff = minpoly(u^per)
                r.append( (ZZ(x0),ZZ(x1),ZZ(-ff[1]),ZZ(-ff[0])) )

    return r

#computes the nth term in recurrent sequence $x_{k+1}=a*x_{k} + b*x_{k-1}$ with initial values $x_0$ and $x_1$
def nthterm(x0, x1, a, b, n):
    return (Matrix([[0,1],[b,a]])^n * vector([x0,x1]))[0]

#Section 3.2: computes terms (up to the N-th term) that are powers of q in recurrent sequence $x_{k+1}=a*x_{k} + b*x_{k-1}$ with initial values $x_0$ and $x_1$
def powersol(x0,x1,a,b,q,N):
    u = x0
    v = x1
    ex = []
    for i in range(N+1):
        if u:
            k = valuation(abs(u),q)
            if abs(u) == q^k:
                ex.append(k)
        u, v = v, a*v + b*u

    return ex

#Section 2
# Input: G, A, B, q defining the equation G*q^z = A*t^2 + B
# Output:
def exp_pol_solve(G, A, B, q):
    print("Solving for [G, A, B, q] = ", [G, A, B, q]);
    SOL = []
    for w in range(2):
        print("Solution parity:", w);
        if (q^w*A*G).is_square():
            # (q^( (z+w)/2) )^2 - (A*q^w) = B* q^w
            # (q^( (z+2)/2) - sqrt( A*q^w) ) * (q^((z+w)/2) + sqrt(A*q^w) ) = B*q^w
            print("Solving difference of squares:", [G*A*q^w, G*B*q^w]);
            # u = isqrt(G*A*q^w);
            if G*B*q^w == 0:
                continue
            if is_prime(G*B*q^w):
                hh = (B/2) +1/(2*G*q^w);
                h = valuation(hh, q);
                if hh == q^h:
                    SOL.extend( [isqrt((G/A)*(q^(2*h+w))-B/A), 2*h+w] )
                    print("SOL = ", SOL);
                continue

            for d in divisors(G*B*q^w):
                #if d*d > G*B*q^w:
                #           next
                # if (G*B*q^w)/d - d == 2*u:
                v = (d + (G*B*(q^w))//d) / (2*G)
                if v == q^valuation(v, q):
                    SOL.append(valuation(v,d))
                    print("SOL = ", SOL);
                    # print( (G*(q*(valuation(v,q)*2) - w))-B)/A);
                    # SOL .append([isqrt((G*(q*(valuation(v,q)*2) - w))-B)/A)), valuation(v,q)*2 - w]);
                    #break
            continue

        r1 = pf_solve(G*q^w, A, B)
        print("Recurrence solutions:", r1)

        qprimes = prime_factors(q)     # in PARI/GP: factor(q)[,1]

        for s in r1:
            #process solution s
            print("Analyzing recurrence: ", s)

            k = 0
            while True:
                k = k+1
                #print("K =", k)
                print(f"Consider sequence modulo {q}^{k}")

                r2 = findij(*s, q^k)


                if k == 1:
                    per = r2[1] - r2[0]
                    print("i,j:", r2)
                    r3 = findzeros(*s, q^k, *r2)
                    print(r3)
                    if r3[0] != []:
                        print("Error: Unsupported singular solutions")
                        raise
                    zi = r3[1]
                else:
                    # construct zi from previous
                    per0 = per
                    per = r2[1] - r2[0]
                    r3 = zi
                    zi = []
                    for i in r3:
                        for j in range(per//per0):
                            if nthterm(*vector(Zmod(q^k),s), i + j*per0) == 0:
                                zi.append(i + j*per0)

                print(f"zero indices: {zi} modulo {per}")
                success = True

                for j in zi:
                    # prove that there are no solution in subsequence defined by j
                    tz1 = abs(nthterm(*s,j))
                    if tz1:
                        assert type(tz1) == Integer
                        print("log10 of first zero:", log(tz1,10).n() )
                        tz2 = nthterm(*vector(Zmod(tz1),s), j + per).lift()
                    else:
                        tz2 = nthterm(*s, j+per)

                    t = gcd(tz1, tz2)
                    print(f"GCD of first two periodic zeros: {t} = {factor(t)}")
                    for q in qprimes:
                        t //= q^valuation(t, q)

                    f = prime_factors(t)      # in PARI/GP: factor(t)[,1]
                    print(t, f)

                    success = False
                    for p in f:
                        print("Testing modulo:", p)
                        r2 = findij(*s, p);
                        perp = r2[1] - r2[0]
                        r3 = findzeros(*s, p, *r2)
                        if r3[0] != []:
                            print("Error: Unsupported singular solutions")
                            raise

                        print("Period:", perp);

                        if per%perp == 0 and j%perp in r3[1]:
                            success = True
                            print(f"Eliminated indices Mod({j}, {per}) with prime {p} whose period is {perp} with zero indices {r3}");
                            break

                    if not success:
                        print(f"Cannot prove that there are no solutions in the subsequence with indices Mod({j}, {per})")
                        k = valuation(tz2, q) if tz1 == 0 else valuation(tz1, q)
                        break                   #in PARI/GP: next(2)

                if success:
                    SOL.extend( map(lambda z: (isqrt((G*q^(2*z+w)-B)/A), 2*z+w), powersol(*s,q,per) ))
                    print("SOL = ", SOL);
                    break

    return set(SOL)
