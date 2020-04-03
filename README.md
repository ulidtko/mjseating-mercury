# Mahjong seating generator in Mercury

What does this program compute?

Tournament grids (player seatings) for the [Riichi Mahjong] game.
Players are represented simply by integers: 1, 2, 3, 4, and so on.
The generated results comprise a full tournament schedule, listing tables of
every hanchan. Each table lists 4 players. Solutions contain no "intersections":
not a single pair of players meet more than once during the whole tournament.

Once compiled, usage is as simple as:

    ./mjseating -P <NUM_PLAYERS> -H <NUM_HANCHANS>

Be aware that the search will likely take a long time. 24-player-6-hanchan
computation been running for *23 to 29 hours* on my machine to find any results.
Smaller parameters of course will run faster. 20-player-5-hanchan solves in <1s.

You'll find samples of generated seatings under `data/`. There's also a little
python helper script to re-check solution correctness (0 intersections).

Please let me know if you find this useful.

[Mercury]: https://mercurylang.org/
[Riichi Mahjong]: https://en.wikipedia.org/wiki/Japanese_Mahjong

## Building ##

Use `mmc` (the Melbourne Mercury Compiler):

    mmc --grade hlc.gc -O2 mjseating

## Tracing (debug logs) ##

    env TRACE=1 ./mjseating -P16 -H4

## Debugging with mdb ##

    mmc --grade reg.gc.decldebug.stseg mjseating.m
    mdb ./mjseating -P16 -H4

Debugging user guide: https://mercurylang.org/information/doc-release/mercury_user_guide/Debugging.html

## Profiling ##

Recompile in a profiling grade:

    mmc --grade reg.gc.profdeep -O2 mjseating.m

Then run. `Deep.data` is written.

To view the profile, Mercury provides `mdprof`... which is a CGI script.

With nginx:

```nginx
        location /cgi-bin/mdprof {
            # spawn-fcgi -u ulidtko -M777 -s /tmp/mdprof-fcgi.sock -- /usr/bin/fcgiwrap -f
            include /etc/nginx/fastcgi_params;
            fastcgi_read_timeout 5s; # default 60s
            fastcgi_param SCRIPT_FILENAME /usr/bin/mdprof_cgi;
            fastcgi_pass unix:/tmp/mdprof-fcgi.sock;
        }
```

and pass full path to `Deep.data` in the URL, e.g: `http://localhost/cgi-bin/mdprof?/home/ulidtko/code/mjseating/Deep.data`


## TODO ##

- [ ] honest JSON output format
- [ ] progress marks ~every 5 minutes
- [ ] shuffle quads with seed
- [ ] parallelize via searching different shuffles/seeds
