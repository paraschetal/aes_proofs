

function = """
Definition nat_to_byte(a : nat) : byte := 
match a with \n"""


for i in range(256):
  s = "{0:b}".format(i)
  sr = ""
  for j in range(8-len(s)):
    sr += "s0 "
  for j in range(len(s)):
    sr += "s"+s[j]+" "
  function += "| "+str(i)+" => bits8 "+sr+" \n"


function += "\n  end."


print(function)

