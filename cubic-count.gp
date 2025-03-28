/* cubic-count.gp: A program to generate numerical data, describing the number
of cubic fields with bounded invariants. Currently this program counts by |D|F,
and can be adapted to count by other invariants as needed.

Some numerical data generated by this program is given in the paper

A. Shankar and F. Thorne, On the asymptotics of cubic fields ordered by general invariants.

Permission is granted to freely use, modify, and/or redistribute this code; if you do, you are requested to cite the above paper when relevant. */

disc_bound = 1000000;

v1 = concat(readvec("icf-1000k.gp"));
v2 = concat(readvec("rcf-1500k.gp"));
v = concat(v1, v2);

DF_bound = 1000;
default_F_bound = 0; /* This turns out to maximize the range we can do */ 
exclude_minus_3 = 1;

read("cm-test.gp");

{
compute_df(disc) = 
  my(c, d, f);
  c = core(disc);
  if (isfundamental(c), d = c, d = 4*c);
  f = round(sqrt(disc/d));
  [d,f];
}

{
DH_compute_results(F_bound) = 
  if (F_bound * DF_bound > disc_bound, print("ERROR. Results unreliable."));
  results = vector(DF_bound);
  for (i = 1, length(v),
    df = compute_df(v[i][3]);
    if ((df[2] <= F_bound) && 
        (abs(df[1]) * df[2]^2 <= disc_bound) && 
        (abs(df[1]) * df[2] <= DF_bound) &&
        ((df[1] != -3) || (! exclude_minus_3)), 
      results[abs(df[1]) * df[2]]++; /*print(df);*/
    );
  );
  results;
}

{
CM_compute_results(F_bound) = 
  results = vector(DF_bound);
  D_bound = truncate(DF_bound / (F_bound + 1));
  for (sig_idx = 1, 2,
    mysig = 2*sig_idx - 3;
    init(mysig);
    for (absd = 1, D_bound,
      if (isfundamental(mysig * absd) && ((absd != 3) || !exclude_minus_3),
        curr_n = truncate(DF_bound/absd);
        dir_series = CM_RHS(mysig * absd, curr_n, 1);
        dir_series[1] -= 1/2;
        for (f = F_bound + 1, curr_n, results[absd * f] = results[absd * f]+dir_series[f]; /*print([mysig*absd,f],":",dir_series[f]) */);
   ));
  );
  results;
}

/* CM_box_count: uses Cohen-Morra to count all with |d| \leq D_bound and f \leq F_bound. */
{
CM_box_count(D_bound, F_bound) = 
  mycount = 0;
  for (sig_idx = 1, 2,
    mysig = 2*sig_idx - 3;
    init(mysig);
    for (absd = 1, D_bound,
      if (isfundamental(mysig * absd),
        dir_series = CM_RHS(mysig * absd, F_bound, 1);
        dir_series[1] -= 1/2;
        for (f = 1, F_bound, mycount = mycount + dir_series[f]);
   ));
  );
  mycount;
}

{
compute_vec(my_df_bound) =
  DF_bound = my_df_bound; 
  DH_results = DH_compute_results(default_F_bound);
  CM_results = CM_compute_results(default_F_bound);
  DH_results + CM_results;
}

EP_factor(p) = (1 + 2/p) * (1 - 1/p)^2;

{
compute_EP_const(lim) = 
  result = 1.0;
  forprime(p = 5, lim, result = result * EP_factor(p));
  result * 2 * (17/9) * (1 - 1/2)^2 * (1 - 1/3)^2 / 3;
}

{
actual_count(X) = 
  vec = compute_vec(X);
  vecsum(vec);
}

{
expected_asym(X) = 
 (compute_EP_const(10000000) + (1 - exclude_minus_3) * .066907733/3) * X * log(X); 
}

{
test(X) = 
  print("X: ", X);
  expcount = expected_asym(X);
  actcount = actual_count(X);
  print("Expected: ", expcount);
  print("Actual: ", actcount);
  print("Ratio: ", actcount/expcount);
  print("Secondary X const: ", (expcount - actcount)/X);
}

{
test2(D_bound, F_bound) = 
  print("|d| \leq ", D_bound, "; f \leq ", F_bound);
  actcount = CM_box_count(D_bound, F_bound);
  expcount = compute_EP_const(1000000) * D_bound * F_bound;
  print("Expected: ", expcount);
  print("Actual: ", actcount);
}

{
test_many() = 
  print("Excluding minus 3:");
  exclude_minus_3 = 1;
  test(100);
  test(1000);
  test(10000);
  test(20000);
  test(30000);
  print("Including minus 3:");
  exclude_minus_3 = 0;
  test(100);
  test(1000);
  test(10000);
  test(20000);
  test(30000);
}
