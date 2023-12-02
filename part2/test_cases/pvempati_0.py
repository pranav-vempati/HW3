# From Nov 17th lecture slides:
for i in range(0, 128):
    a[i%64] = a[i+64]*2
