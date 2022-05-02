# could optimize this to cache for the n's we need and then just call it later
def construct_tree(n):
  leaf = "destruct b15. reflexivity. reflexivity. "
  if n > 15:
    return ""
  if n == 15:
    return leaf
  current_string = ""
  for i in range(n,16):
    current_string += "destruct b"+str(i)+". " 
  current_string += "reflexivity. reflexivity. "
  return construct_tree(n+1) + current_string + construct_tree(n+1)



s = ""
for i in range(15, -1, -1):
  # construct a tree with the top node being i-1->15
  for j in range(i, 16):
    s+= "destruct b" + str(j)+". "
    
  s+=  "reflexivity. reflexivity. "
  
  s+=construct_tree(i+1)
  s+= "\n"
  
# print(s)
with open ("proof_output2.txt", "w") as f:
    f.write(s)

