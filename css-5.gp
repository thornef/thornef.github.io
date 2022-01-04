\\ count_s3_sextic.gp: (or css.gp for short!)
\\ css-5.gp: A variant to compute in arithmetic progressions mod 5.
\\ As described in my paper with Takashi, we avoid all cubic fields ramified at 2 or 3.

\\ See css-old.gp for a version which was simpler, more elegant, and
\\ worked, but which used a ton of memory (and thus didn't work for large X.)

\\ Computes the number of S_3-sextic fields whose discriminant is bounded by X, as a function of X.
\\ The main tool is an exact formula for the number of cubic fields of given resolvent,
\\ namely Theorem 2.5 of http://arxiv.org/pdf/1301.3563v1.pdf. The program relies on a list of
\\ all cubic fields of discriminant < Y, which we have thanks to Karim Belabas.

\\ Sometimes the program will output error messages without halting; if so, then the output
\\ of the program is not to be trusted.

\\ BACKGROUND INFORMATION. (See http://arxiv.org/pdf/1208.2170.pdf)
\\ There is a bijection between non-cyclic cubic fields K, up to isomorphism, 
\\ and their Galois closures S_3-sextic fields K'. The discriminants of these fields
\\ are related by the formula
\\
\\ Disc(K') = \Disc(K)^2 \Disc(F),
\\
\\ where F is the quadratic resolvent field of F. We may rewrite this formula by noting that
\\ \Disc(K) = \Disc(F) f(K)^2, where f(K) is the conductor, and so we obtain
\\
\\ Disc(K') = \Disc(F)^3 f(K)^4.
\\
\\ Our revised algorithm is the following.

\\ (1) Iterate over a table of cubic fields. The table needs to contain
\\ all cubic fields with discriminant up to 27 * X^{1/3}. (With a little 
\\ bit more work, we could handle fields with f(K) = 1 directly, instead of 
\\ using the formula, and so make do with a little bit less.)
\\
\\ We rely on Belabas's work for this. For each cubic field E, we determine
\\ whether its discriminant is D^* or -27D for a fundamental discriminant 
\\ D. If not, toss it.

\\ (2) For each cubic field we keep, compute the corresponding term in (2.2),
\\ where the number of terms is determined by the bound
\\ f(K) < X^{1/4} / \Disc(F)^{3/4}. This requires understanding the arithmetic
\\ of cubic fields of discriminant Disc(F)* and -27 Disc(F).
\\
\\ Then, compute the partial sum of the Dirichlet series, and keep a running total of all
\\ such. (This concludes our iteration over the table of cubic fields.)

\\ (3) Compute the main terms in (2.2), take the partial sums, and sum over D. Add this
\\ to the total from (2).

\\ A kludge:
\\ If I am not mistaken, PARI/GP does not have the ability to read in very large files sequentially. We work 
\\ assume that they are broken up into moderately large files.
\\ We assume the following: The input is stored in files named "[input_file_base]-#.gp", where input_file_base
\\ may be set below, and the #'s are numerals starting at 1, and going through num_input_files. It is
\\ reasonable for these files to contain on the order of 10^6 fields. Each file contains vectors of the form
\\ [a, b, c, d], so that ax^3 + bx^2 + cx + d is a generator of the cubic field, and the polynomial
\\ discriminant is the same as the field discriminant. Each occurs on its own line and these are separated
\\ by newlines.

\\ The order of the fields, and which fields appear in each file, is irrelevant.

\\ A separate program is required, and included, to parse the output of Karim Belabas's "cubic" program 
\\ and produce such files. 

input_file_base = "T33-107";
num_input_files = 1;
disc_bound = 10^7; \\ Warning: This is never actually used except to generate error messages.
field_sign = 1; \\ The sign of the discriminants in the file.
                 \\ Note: This will let us count cubic fields of the OPPOSITE sign.

\\ is_disc_good: D is the discriminant to be considered, and X is the eventual bound. X_13 is the cube root of X, which it saves time to precompute.
\\ Determines whether D is equal to (D')* or -27D' for some fundamental discriminant D'. If yes,
\\ returns D', otherwise, returns 0.

\\ if good, returns the associated fundamental discriminant.
{
is_disc_good(D, X_13) = 
  local(tf, retval, ifd, absD);
  retval = 0;
  if (gcd(2, D) == 1,
   tf = gcd(81, D);
   ifd = isfundamental(D);
   absD = abs(D);
   if (ifd, 
     if (tf == 3,
       retval = if( absD <= 3*X_13[length(X_13)], -D/3, 0));
   );
   if (! ifd,
     if (tf == 27,
       retval = if( isfundamental(-D/27) && (absD <= 27*X_13[length(X_13)]), -D/27, 0));
   );
  );
  retval;
}

{
compute_disc(CF) = 
  CF[2]^2*CF[3]^2 - 4*CF[1]*CF[3]^3 - 4*CF[2]^3*CF[4] - 27*CF[1]^2*CF[4]^2 + 18*CF[1]*CF[2]*CF[3]*CF[4];
}


{
omega_E(E, p) = 
  local(id, retval);
  if (gcd(p, E.disc) == p, print("Error: ramified field unexpected."));
  id = idealprimedec(E, p);
  if (length(id) == 3, retval = 2);
  if (length(id) == 1, retval = -1);
  retval;
}

{
c_D(D) = 
  local(result);
  if (D > 0 || D == -3, result = 3);
  if (D < -3, result = 1);
  result;
}

\\ Compute the main term of Theorem 2.5, as a Dirichlet series.
\\ Works for quadratic resolvent D, and computes to a length of N.

\\ This (and in particular the inner loop) is the efficiency bottleneck.
\\ For N = 10^6 it takes roughly 2-5 seconds on my computer, and the running time
\\ is roughly linear in N (as I discovered by experiment).
\\ 
{
compute_main_dirichlet(D, N) = 
  local(EP1, p1, temp, i, i_backwards, initial_factor);
  EP1 = vector(N);
  EP1[1] = 1/(2 * c_D(D));
  \\EP1 = dirmul(EP1, M_one(D, N));
  for (p1 = 5, N,
    if (isprime(p1), 
     if (kronecker(-3*D, p1) == 1, \
        \\ Over this loop we basically want to do another dirmul. But that is terribly
        \\ inefficient, so we do it by hand.
        for (i = 1, truncate(N/p1), 
          i_backwards = truncate(N/p1) + 1 - i; \\ do it backwards, to let us write over the same array
          EP1[i_backwards*p1] = EP1[i_backwards*p1] + 2*EP1[i_backwards];
        );
  )));
  EP1;
}  

\\ Compute an extra term of Theorem 2.5, as a Dirichlet series.
\\ D and N are as in the main term. E is the data of a cubic field (and E_disc
\\ is its discriminant, which we have computed already)

\\ (Note: This is half copy-and-pasted from the previous function, which could
\\ be avoided with more effort)
{
compute_twisted_dirichlet(D, N, E) =
  local(EP1, p1, i, i_backwards);
  EP1 = vector(N);
  EP1[1] = 1/c_D(D);
  \\EP1 = dirmul(EP1, M_two_E(D, N, E));
  for (p1 = 5, N,
    if (isprime(p1), 
     if (kronecker(-3*D, p1) == 1, \
        for (i = 1, truncate(N/p1), 
          i_backwards = truncate(N/p1) + 1 - i; \\ do it backwards, to let us write over the same array
          EP1[i_backwards*p1] = EP1[i_backwards*p1] + omega_E(E, p1) * EP1[i_backwards];
        );
  )));
  EP1;
}  

\\ Input: v and N are both vectors, with N sorted. Returns a vector of the same length as N.
\\ If, e.g. N = [3, 4, 5] then the output is [v_1 + v_2 + v_3, v_1 + .. + v_4, v_1 + .. + v_5].

\\ Also splits the output mod 5.
{
vector_add_5(multiple_5, v, N) = 
  local(i, retval);    
  retval = matrix(length(N), 5);
  placeholder = 1;
  \\print("v = ", v, "; N = ", N, "; multiple_5 = ", multiple_5);
  for (i = 1, length(v), 
    mod5 = lift(Mod(i^4 * multiple_5, 5));
    if (mod5 == 0, mod5 = 5);
    while (i > N[placeholder], placeholder = placeholder + 1);
    for (j = placeholder, length(N), retval[j, mod5] = retval[j, mod5] + v[i]);
  );
  \\print(retval);
  retval;
}

\\ note [elaborate]: X is a vector here.
{
compute_S3(X) = 
  local(i, j, running_total, fd, field_disc, related_fd, E, redundant, N, maxN X_13, dir_ser, partial_sum, v, input_file_name_curr); 
  local(maxX_index);
  compute_sign = - field_sign;
  running_total = matrix(length(X), 5);
  X = vecsort(X);

  \\ Some quantities which it is inefficient to compute very many times:
  X_13 = X^(1/3);
  X_13t = truncate(X^(1/3));
  X_14 = X^(1/4);
  if (disc_bound / 27 < X_13[length(X)], print("Error: Can only compute up to ", disc_bound^3 / 3^9, "."));

  for (i = 1, num_input_files, 
    input_file_name_curr = concat(input_file_base, concat("-", concat(i, ".gp")));
    print("Reading input file ", input_file_name_curr, "...");
    v = readvec(input_file_name_curr);
    for (j = 1, length(v), 
      field_disc = compute_disc(v[j]);
      related_fd = is_disc_good(field_disc, X_13); \\ related fundamental discriminant. ("fd" has two meanings)
      if (related_fd != 0, \\ note: manipulate the polynomial slightly to make monic and avoid a warning.
        E = nfinit(x^3 +  v[j][2] * x^2 + v[j][1] * v[j][3] * x + v[j][1]^2 * v[j][4]);
        N = truncate(X_14 / abs(related_fd)^(3/4)); 
        \\print("related_fd = ", related_fd, "; N = ", N);
        dir_ser = compute_twisted_dirichlet(related_fd, N[length(X)], E);
        partial_sum_5 = vector_add_5(Mod(related_fd, 5)^3, dir_ser, N); \\ no a priori reason this should be positive, by the way.
	running_total = running_total + partial_sum_5;
        \\print(running_total);
    ));
  );

  for (D = 5, X_13t[length(X_13t)],
    if (isfundamental(compute_sign * D) && gcd(D, 6) == 1,
      N = truncate(X_14 / D^(3/4)); 
      dir_ser = compute_main_dirichlet(compute_sign * D, N[length(X)]);
      partial_sum_5 = vector_add_5(Mod(compute_sign * D, 5)^3, dir_ser, N);
      running_total = running_total + partial_sum_5;
      mcs = lift(Mod(compute_sign * D, 5)^3);
      if (mcs == 0, mcs = 5);
      for (j = 1, length(X), 
        if (N[j] > 0, running_total[j, mcs] = running_total[j, mcs] - 1/2));
  ));
  for (i = 1, length(X), 
   for (j = 1, 5, 
    print("Number of fields with |Disc(K)| < ", X[i], "; sign = ", \
      compute_sign, " modulus = ", j, ": ", running_total[i, j]);
  ));
}

cs(X) = compute_S3(X);
Xtemp = [1, 2, 5];
Xtest = vector(18);
for (ii = 1, 6, for (jj = 1, 3, Xtest[3*(ii - 1) + jj] = 10^(10 + ii)*Xtemp[jj]));

