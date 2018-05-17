function toto()
   return 1,2;
end

-- comment

function lua_sample()
   print ("HELLO MAXIME");
   sec, nsec = time_get();
   sec = sec + 5;
   time_delay_until (sec, nsec);
   a,b = toto ();
   print ("r1  : " .. a .. "r2 : " .. b);
end

