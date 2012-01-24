print ("Hello from ping.lua");

data_source = 10;

function do_ping ()
   data_source = math.random(1, 100);
end

function receive_ping (val)
   print ("value : " .. val);
end
