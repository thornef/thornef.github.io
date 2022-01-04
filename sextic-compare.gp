
curr_sign = -1;
C = 0; K = 0;

cyclic_const = 0.158528258396; \\ # cyclic fields is this const * x^(1/2).
\\ see Cohen, Diaz y Diaz, Olivier, "Counting discriminants of number fields".

non_uniformity_fix = 0; \\ see below

{
set_constants() =
  C = if (curr_sign == 1, 1, 3);
  K = if (curr_sign == 1, 1, sqrt(3));
}

constant_accuracy = 10000;

\\ Note: If this program is called by sextic.gp, then after this program is loaded these values
\\ will be overwritten with the values of r_exclude there.

\\ note: this program has not been tested recently with these values set to anything other than 0.
exclude_3 = 1; \\ if =1, exclude everything divisible by 3
exclude_2 = 1;
exclude_tr = 0; \\ if 1, exclude fields totally ramified anywhere. ASSUMES 2 and 3 are EXCLUDED (for now)
special_5 = 1; \\ (this was for a special test, should be 0)

\\ determine the number of S_3 sextic fields up to discriminant X
\\ (assuming we are given a finite list of them!)

\\ is_square: test if n is a square
is_square(n) = (core(n) == 1);

\\ **********************************************************************
\\ Constant computing functions:
\\ Compute the functions c(p), k(p), and their products, as defined in [TT].
\\ They are as in [TT] if the constants exclude_3, exclude_2, exclude_tr are equal to 0.
\\ If we set any of the constants equal to 1, then we compute a limited count of fields.
\\ **********************************************************************

\\ c(p): The constant c(p) appearing in [TT].
\\ The constant is as in the paper if exclude_3, exclude_2, and exclude_tr are all zero.
\\ If any of these are 1, then c(p) is modified to exclude primes as indicated.
{
c(p) = 
  local(result);
  if (p == 3,
    if (exclude_3, result = 2/3, result = (2/3)*(4/3 + 3^(-5/3) + 2*3^(-7/3))));

  if (p > 3 ||((p == 2) && (exclude_2 == 0)), 
    result = (1 - p^(-1))*(1 + p^(-1) + p^(-4/3)));
  \\ variation: multiply by a fudge factor: don't allow any totally ramified primes!
  \\ If we do this, it is assumed that we are also excluding 2 and 3.
  if ((p > 3) && (exclude_tr == 1), 
    result = result * (1 + p^(-1))/(1 + p^(-1) + p^(-4/3)));

  if ((p == 2 && exclude_2 == 1), result = (1 - p^(-1)));
  result;
}

\\ c_modified:
\\ c(p) is close to (1 - p^(-4/3))^(-1) for p large. multiply by this factor
\\ to get something closer to 1 and so make the product converge faster.
\\ in particular, c_modified(p) = 1 + O(p^-2).
\\ later, we will multiply by zeta(4/3).

c_modified(p) = c(p) * (1 - p^(-4/3));

\\ some placeholder variables
prod_cp = 1;
prod_kp = 1;
\\ Compute \prod c_p, times an error of (1 + O(cutoff^(-1)))
{
compute_prod_cp(cutoff) = 
  local(result);
  result = 1;
  for (i = 2, cutoff, 
    if (isprime(i), result = result * c_modified(i));
  );
  result = result * zeta(4/3);
  prod_cp = result;
}

\\ compute the k_3 constant if we exclude 3.
\\ this is a little bit ugly, as I could calculuate it from scratch.

temp1 = (1 + 3^(-1/3))*(1 + 3^(-2/3)); \\ UR
temp2 = (1/3)*(1 + 3^(-1/3))^2; \\ singly ram
temp3 = (1/9)*(1 + 3^(-1/3))*(2*3^(-4/9) + 3^(1/9));
k3_fudge_factor = temp1/(temp1 + temp2 + temp3);

\\ The constant k(p) defined in my paper with Takashi, and admitting variations if we exclude 2 and/or 3 (as with c(p))
{
k(p) = 
  local(result);
  \\ This is the factor k_3.
  if (p == 3,
    result = 0.25 * (11/3 - 3^(-2/3) + 3^(-8/9) + 2/3^(13/9) - 3^(-14/9) - 2*3^(-19/9))); \\ from Takashi's paper
  \\ Except, if we want to exclude everything ramified at 3, multiply by a fudge factor.
  if (p == 3 && exclude_3 == 1,
    result = result * k3_fudge_factor);

  \\ This is the factor k_p.
  if (p != 3,
    result = 1 + (p^(-13/9)/(1 + p^(-1)))*(1 - p^(-2/9) - p^(-5/9) - p^(-2/3)));
  \\ Similarly, we might exclude everything ramified at 2.
  if (p == 2 && exclude_2 == 1,
    fudge_factor = (1 + p^(-2/3))/(1 + p^(-2/3) + p^(-1) + p^(-4/3) + p^(-13/9));
    result = result * fudge_factor;
  );
  \\ For primes > 3, we have the option of throwing out the totally ramified primes but keeping the partially ramified ones.
  if ((p > 3) && (exclude_tr == 1),
    fudge_factor = (1 + p^(-2/3) + p^(-1) + p^(-4/3))/(1 + p^(-2/3) + p^(-1) + p^(-4/3) + p^(-13/9));
    result = result * fudge_factor;
  );
  result;
}

\\ see c_modified(p). We need two fudge factors to get the error down to O(p^-2).
k_modified(p) = k(p) * (1 - p^(-13/9)) / (1 - p^(-15/9));

{
compute_prod_kp(cutoff) = 
  local(result);
  result = 1;
  for (i = 2, cutoff, 
    if (isprime(i), result = result * k_modified(i));
  );
  result = result * zeta(13/9) / zeta(15/9);
  prod_kp = result;
}


\\ **********************************************************************
\\ (fill in a comment here!!!)
\\ **********************************************************************

\\ evaluate the integral \int_{n^{\infty}} t^{-pow} / (log t) dt.
\\ gives poor results if pow is close to 1.
\\ splits it up into a ton of intervals and adds them up.
{
evaluate_mod_li(pow, n) =
  local(i, c, X);
  base = n^(1 - pow)/((pow - 1)*(log(n)));

  c = 1.005;
  base2 = 0;
  for (i = 0, 10000, \
    X = n*c^i;
    base2 = base2 + (X^(1 - pow) / (1 - pow)) * (c^(1 - pow) - 1) / log(X);
  );
  base2;
  \\print("base : ", base);
  \\print("base2 : ", base2);
}

\\ compute_predicted_num_fields(n):
\\ Using [TT] and the constants above, computes the expected number of S_3 extensions whose
\\ discriminant is bounded by X.

\\ PARAMETERS (global variables):
\\ curr_sign is -1 or 1. sign of the discriminants being counted. if 1, we have to subtract the contribution of cyclic fields.
\\ non_uniformity_fix is 0, 1, or 2. If 0, just take the main terms of order n^(1/3) and n^(5/18).
\\ if equal to 1 or 2, then add additional correction terms, corresponding to the fact that no prime > X^(1/4) can totally ramify.
\\ if equal to 1, then use correction terms of 1 - 12*n(-1/12)/log(n) and 1 - 9*n^(-1/9)/log(n) for the main and secondary terms
\\ respectively.
\\ if equal to 2, use the actual integrals which give these terms. this is something like evaluating li(x) instead of just writing
\\ x/log(x).
\\ non_uniformity_const: In fact, no prime > (X/non_uniformity_const)^(1/4) can totally ramify. Compute with this.

{
compute_predicted_num_fields(n) = 
  local(a, b, cc, i, num_cyclic);
  compute_prod_cp(constant_accuracy);
  compute_prod_kp(constant_accuracy);
  \\if (non_uniformity_fix == 1, \
  \\  cc = round((n/25)^(1/4));
  \\  for (i = cc, 4*cc^2, if (isprime(i), \
  \\    C = C * (1 + i^(-1))/(1 + i^(-1) + i^(-4/3));
  \\)));
  a = C/12;
  b = 4*K*zeta(1/3)/(5*gamma(2/3)^3);
  if (special_5 == 1, \
    a_mod = 1/(1 + 5^(-1) + 5^(-4/3));
    b_mod = (1 + 5^(-2/3))/(1 + 5^(-2/3) + 5^(-1) + 5^(-4/3) + 5^(-13/9));
    a = a * a_mod/4; b = b * b_mod/4;
  );
  if (special_5 == 2, \
    a_mod = 1 - 1/(1 + 5^(-1) + 5^(-4/3));
    b_mod = 1 - (1 + 5^(-2/3))/(1 + 5^(-2/3) + 5^(-1) + 5^(-4/3) + 5^(-13/9));
    a = a * a_mod; b = b * b_mod;
  );

  num_cyclic = 0;
  if (curr_sign == 1, num_cyclic = cyclic_const * (1/3) * n^(1/4));
  if (non_uniformity_fix == 0, non_uniformity_const = 1); \\ mainly just to make sure we don't divide by zero.
  nmod = n/non_uniformity_const;
  if (non_uniformity_fix == 0,
    retval = a*prod_cp*n^(1/3) + b*prod_kp*n^(5/18) - num_cyclic);
  if (non_uniformity_fix == 1,
    retval = a*prod_cp*n^(1/3)*(1 - 12*nmod^(-1/12)/log(nmod)) + b*prod_kp*n^(5/18)*(1 - 9*nmod^(-1/9)/log(nmod)) - num_cyclic);
  if (non_uniformity_fix == 2,
    retval = a*prod_cp*n^(1/3)*(1 - evaluate_mod_li(4/3, (nmod)^(1/4))) + b*prod_kp*n^(5/18)*(1 - evaluate_mod_li(13/9, (nmod)^(1/4))) - num_cyclic);
  retval;
}

\\ for quick and dirty testing.
{
cpnf(n) = 
  set_constants();
  compute_predicted_num_fields(n);
}

\\*******************************
\\ list_results(): 
\\ see definitions of the parameters above.
{
list_results(nuf, nuf_const, sgn) =
  local(i);
  curr_sign = sgn;
  non_uniformity_fix = nuf;
  non_uniformity_const = nuf_const;
  set_constants();
  for (i = 10, 18, \
    predicted = compute_predicted_num_fields(10^i); \\ Takashi's note, residues of Shintani zeta functions, etc.
    print("X = 1 * 10^", i, "; predicted = ", predicted);
    predicted = compute_predicted_num_fields(2 * 10^i); \\ Takashi's note, residues of Shintani zeta functions, etc.
    print("X = 2 * 10^", i, "; predicted = ", predicted);
    predicted = compute_predicted_num_fields(3 * 10^i); \\ Takashi's note, residues of Shintani zeta functions, etc.
    print("X = 3 * 10^", i, "; predicted = ", predicted);
    predicted = compute_predicted_num_fields(4 * 10^i); \\ Takashi's note, residues of Shintani zeta functions, etc.
    print("X = 4 * 10^", i, "; predicted = ", predicted);
    predicted = compute_predicted_num_fields(5 * 10^i); \\ Takashi's note, residues of Shintani zeta functions, etc.
    print("X = 5 * 10^", i, "; predicted = ", predicted);

  );
}

\\*******************************
\\These are a couple of old procedures that compare the predicted number of S_3 fields with the actual.
\\However, these aren't used any more. If they are used, then one needs to provide a sorted list of field
\\discriminants so we can compare with them. (When I wrote this function, this file was being called from another
\\PARI/GP file, but now I have a Java program to count the S_3 discriminants.)


\\allocatemem(12!); -- no longer allowed in new version
input_filename = "new-sorted.gp"; \\ default; can override, see sortr
sorted_input_provided_without_file = 0; \\ set to 1 if some other file is going to set sorted_input

\\ fields_up_to(n): Returns the count of fields of discriminant < n, provided in sorted_input.
\\ If the field is cyclic then it is counted with a weight 1/3 (with a stray "print" for now...)

\\ If -1 is returned, then the procedure has terminated in an error.
{
fields_up_to(n) = 
  local(max_val,i,ans);
  max_val = sorted_input[length(sorted_input)];
  if (n > max_val, ans = -1); \\ abort. 
  if (n <= max_val,
    ans = 0;
    \\ This is really slow and should be improved for efficiency if we get lots of data.
    for (i = 1, length(sorted_input),
      if (sorted_input[i] < n, 
        if (is_square(sorted_input[i]) && (curr_sign == 1), ans = ans + 1/3; print(sorted_input[i]), ans = ans + 1);
   ));
  );
  ans;
}

\\ compare_results: Computes the predicted and actual number of S_3 extensions nad compares the results.
{
compare_results(n) = 
  predicted = compute_predicted_num_fields(n); \\ Takashi's note, residues of Shintani zeta functions, etc.
  actual = fields_up_to(n); \\ the actual number of fields
  if (actual > -1, print("X = ", n, "; predicted = ", predicted, "; actual = ", actual));
}

