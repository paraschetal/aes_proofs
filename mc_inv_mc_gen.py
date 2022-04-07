# could optimize this to cache for the n's we need and then just call it later
def construct_tree(n):
  leaf = "destruct b31. reflexivity. reflexivity. "
  if n == 31:
    return leaf
  current_string = ""
  for i in range(n,32):
    current_string += "destruct b"+str(i)+". " 
  current_string += "reflexivity. reflexivity. "
  return construct_tree(n+1) + current_string + construct_tree(n+1)



s = ""
for i in range(20, -1, -1):
  # construct a tree with the top node being i-1->31
  for j in range(i, 32):
    s+= "destruct b" + str(j)+". "
    
  s+=  "reflexivity. reflexivity. "
  s+=construct_tree(i+1)
  s+= "\n"
  
# print(s)
with open ("proof_output.txt", "w") as f:
    f.write(s)

