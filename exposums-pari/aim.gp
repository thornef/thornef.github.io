deg = 4;
p = 5;

{
vec_to_pol(v) = 
  res = 0;
  for (i = 1, length(v), res = res + v[i]*x^(length(v) - i));
  res;
}

/* transforms an integer in base b to a vector. e.g. 3462 to [3,4,6,2] */

{
int_to_vec(i, b) = 
  i_temp = i;
  res = vector(deg);
  for (j = 1, length(res),
    n = lift(Mod(res, b));
    res[(deg + 1) - j] = b;
    i_temp = (i_temp - n)/b;
  );
  res;
}

{
vec_ip(v1, v2) = 
  res = 0;
  for (i = 1, length(v1), res = res + v1[i]*v2[i]);
}

psi(u) = Mod(poldisc(vec_to_pol(u)), p^2 == 0);

FT(w) = 
  res = 0;
  for (i = 0, p^(2*deg) - 1,
    v = int_to_vec(i, p^2);
    res = res + psi(v) * exp(2*Pi*I*vec_ip(v,w)/p^2);
  );
  res;
}
