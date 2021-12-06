module example.com/shopcart

go 1.17

replace github.com/UBC-NSS/pgo/distsys => ../../distsys

replace benchmark => ../common

require github.com/UBC-NSS/pgo/distsys v0.0.0-20211101232000-7978191b68b7

require benchmark v0.0.0-00010101000000-000000000000
