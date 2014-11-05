let rec id x = x in
print_int ((id 32768) + (id 32767) + (id 32769) + (id (-32768)) + (id (-32767)) + (id (-32769)))
