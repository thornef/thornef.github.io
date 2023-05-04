c111 = -100;
c21 = -99;
c3 = -98;
c121 = -97;
c13 = -96;

/* cm-test.gp: A program to numerically test the extended Cohen-Morra formula as given in Theorem 11 of

A. Shankar and F. Thorne, On the asymptotics of cubic fields ordered by general invariants.

Permission is granted to freely use, modify, and/or redistribute this code; if you do, you are
requested to cite the above paper when relevant. */


/** change this as desired: 1 is totally real, -1 is imaginary.**/
sig = -1;

{
init(mysig) = 
  sig = mysig;
  if (mysig == -1, 
    maxdisc = 1000000;
    maxmirrordisc = 1500000;
    field_data = read("icf-1000k.gp");
    mirror_field_data = read("rcf-1500k.gp");
  );
  if (mysig == 1, 
    maxdisc = 1500000;
    maxmirrordisc = 1000000;
    mirror_field_data = read("icf-1000k.gp");
    field_data = read("rcf-1500k.gp"); 
  );
}

init(sig);

{
cD(D) = 
  my(res);
  if (D == 1, res = 1);
  if (D < -3, res = 1);
  if (D == -3, res = 3);
  if (D > 1, res = 3);
  res;
}

{
split_type(K, p) = 
  my(data, res);
  res = 0;
  data = idealprimedec(K, p); 
  if (length(data) == 3, res = c111);
  if (length(data) == 2, 
    if (data[1][4] == 2, res = c21);
    if (data[2][4] == 2, res = c21);
    if (data[1][3] == 2, res = c121);
    if (data[2][3] == 2, res = c121);
  );
  if (length(data) == 1,
    if (data[1][4] == 3, res = c3);
    if (data[1][3] == 3, res = c13);
  );
  res;
}

{
omega_E(K, p) = 
  my(st, res);
  st = split_type(K, p);
  res = 0; 
  if (st == c3, res = -1);
  if (st == c111, res = 2);
  res;
}

/* ----- */
/* field_list(D, f): Computes a list of all cubic fields in the database
whose discriminant is -D/3, -3D, or -27D times the square of any divisor
of f. */

{
field_list(D, f) = 
  /* Create a list of field discriminants to check against. */
  f_no_3 = (if (Mod(f, 3) == 0, f/3, f));
  divs = divisors(f_no_3); 

  divs_squared = vector(length(divs));
  for (i = 1, length(divs), divs_squared[i] = divs[i]^2);
  if (Mod(D, 3) == 0, test_list = (-D/3)*divs_squared);
  if (Mod(D, 3) != 0, test_list = (-3*D)*divs_squared);
  test_list = concat(test_list, (-27*D)*divs_squared);
  if (Mod(f, 3) == 0, test_list = concat(test_list, (-243*D)*divs_squared));

  /* worked when coprime to 3 
  test_list = vector(2*length(divs));
  if (Mod(D, 3) == 0,
    for (i = 1, length(divs),
       test_list[i] = (-D/3)*divs[i]^2);
  );
  if (Mod(D, 3) != 0, 
    for (i = 1, length(divs),
       test_list[i] = (-3*D)*divs[i]^2);
  );
  for (i = 1, length(divs),
    test_list[length(divs) + i] = (-27*D)*divs[i]^2;
  );
  */

  absmaxdisc = abs(27*D*f^2);

  /* Now check everything. */
  res = [];
  for (i = 1, length(mirror_field_data), 
    for (j = 1, length(test_list),
      if (mirror_field_data[i][3] == test_list[j], 
        res = concat(res, mirror_field_data[i][2]))); 
    if (abs(mirror_field_data[i][3]) > absmaxdisc, 
      i = length(mirror_field_data) + 1; \\ shortcut the loop
    );
  );
  res;
}

/* primes_split: determines whether every prime divisor of f
   splits in the field described by the polynomial poly. */

{
primes_split(poly, f) = 
  my(K, divs, i, res);
  K = bnfinit(poly);
  divs = divisors(f);
  res = 1;
  for (i = 1, length(divs),
    if (isprime(divs[i]),
      res = res * (split_type(K, divs[i]) == c111);
  ));
  res;
}

/* CM_LHS: Compute the LHS of the generalized Cohen-Morra formula.
   n: How long of a Dirichlet series to compute.
   f: demand that every prime divisor of f split completely.
*/

{
CM_LHS(D, n, f) = 
  my(res);
  if (abs(D) * n^2 > maxdisc, print("ERROR. n too large, results unreliable."));
  if (D/abs(D) != sig, print("ERROR. Opposite signature expected, hardcoded in file."));
  if (!isfundamental(D), print("ERROR. Fundamental discriminant expected."));
  res = vector(n);
  res[1] = 1/2;
  test_idx = 1;
  for (i = 1, length(field_data), 
    while (abs(field_data[i][3]) > abs(D*test_idx^2), test_idx++);
    if (field_data[i][3] == D*test_idx^2, 
      if (primes_split(field_data[i][2], f),
        res[test_idx]++;
    ));
    if (test_idx > n, i = length(field_data) + 1); \\ shortcut the loop
  );
  res;
}

{
M1(D, n, f) =
  my(res);
  res = vector(max(n,9)); 
  if (Mod(f, 3) == 0, res[1] = 1);
  if (Mod(f, 3) != 0,
    if (Mod(D, 3) != 0, res[1] = 1; res[9] = 2);
    if (Mod(D, 9) == 3, res[1] = 1; res[3] = 2);
    if (Mod(D, 9) == 6, res[1] = 1; res[3] = 2; res[9] = 6);
  );
  if (n < 9, res = res[1..n]);
  res;
}

{
M2(D, E, n, f) =
  my(res);
  res = vector(max(n,9));
  if (Mod(f, 3) == 0, res[1] = 1);
  if (Mod(f, 3) != 0,
    Edisc = E.disc;
    if (Mod(D, 3) != 0, 
      if (Mod(Edisc, 27) == 0, res[1] = 1; res[9] = -1);
      if (Mod(Edisc, 27) != 0, res[1] = 1; res[9] = 2);
    ); 
    if (Mod(D, 9) == 3, 
      if (Mod(Edisc, 27) == 0, res[1] = 1; res[3] = -1);
      if (Mod(Edisc, 27) != 0, res[1] = 1; res[3] = 2);
    ); 
    if (Mod(D, 9) == 6, 
      if (Mod(Edisc, 27) == 0, res[1] = 1; res[3] = -1);
      if (Mod(Edisc, 27) != 0, res[1] = 1; res[3] = 2; res[9] = 3*omega_E(E, 3));
    );
  );
  if (n < 9, res = res[1..n]);
  res;
}

{
one_EP(coeff_fn, D, n, f) = 
  my(res);
  res = vector(n);
  res[1] = 1;
  forprime (p1 = 2, n,
    if (kronecker(-3*D, p1) == 1, 
    if (Mod(f, p1) != 0,
      to_mul = vector(n);
      to_mul[1] = 1;
      to_mul[p1] = coeff_fn(p1);
      res = dirmul(res, to_mul);
  )));
  res;
}

/* CM_iszero: Determines if the Cohen-Morra Dirichlet series is identically zero (except for the constant term). */

{
CM_iszero(D, f) = 
  my(divs, i, res);
  divs = divisors(f);
  res = 1;
  for (i = 1, length(divs),
    if (isprime(divs[i]),
      res = res * (kronecker(D, divs[i]) == 1);
  ));
  1 - res;
}

/* CM_RHS: Compute the RHS of the generalized Cohen-Morra formula.
   n: How long of a Dirichlet series to compute.
   f: demand that every prime divisor of f split completely.
*/

{
CM_RHS(D, n, f) = 
  my(res, isszero);
  iszero = CM_iszero(D, f);
  if (iszero, res = vector(n); res[1] = 1/2);
  if (!iszero,
    if (abs(D)*f^2*27 > maxmirrordisc, print("ERROR. f too large, results unreliable."));
    res = (1/2)*dirmul(M1(D, n, f), one_EP(p->2, D, n, f));
    myfields = field_list(D, f);
    for (i = 1, length(myfields), 
      E = bnfinit(myfields[i]);
      res = res + dirmul(M2(D, E, n, f), one_EP(p->omega_E(E, p), D, n, f));
    );
    res = res * (1/cD(D)) * (1/3)^omega(f);
  );
  res;
}

{
test(D, n, f) = 
  LHS = CM_LHS(D, n, f);
  RHS = CM_RHS(D, n, f);
  (LHS - RHS) == vector(n); /* this works because the right side will be all zeros */
}

{
test_lots() = 
  for (absD = 1, 200, 
    D = sig * absD;
    if (isfundamental(D), 
      n = floor(sqrt(maxdisc/absD));
      f_limit = floor(sqrt(maxmirrordisc/(27*abs(D))));
      for (f = 1, f_limit,
         if (issquarefree(f), 
            if (test(D, n, f) == 0,
               print([D, n, f]));  
  ))));
}
         