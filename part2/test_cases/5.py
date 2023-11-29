for i in range(7,10):
    for j in range(5,500):
        for k in range(i,10):
            a[i*j*k] = a[k]

#     i  j  k
# t1: 7, 5, 7
# t2: 8, 5, 8
#       ---
# t1: 7, 5, 8
# t1: 7, 5, 9 #scheduled by OS before next thread
# t2: 8, 5, 9
