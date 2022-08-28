# Steam ID type and accessories

This project provides the `SteamID` type with conversion methods to convert between different Steam ID formats.

Hosted on [GitHub](https://github.com/JohnPeel/steamid-rs).

## Examples and Usage

### Initialize from steam64id
```rust
# use steamid::SteamID;
let steamid = SteamID::new(76561198181797231);
```

### Parse a steam2id
```rust
# use steamid::SteamID;
let steamid = SteamID::parse_steam2id("STEAM_0:0:12345")?;
```

### Parse a steam3id
```rust
# use steamid::SteamID;
let steamid = SteamID::parse_steam3id("[U:1:12345]")?;
```

### steam64id to steam2id
```rust
# use steamid::SteamID;
let steamid = SteamID::new(76561198181797231);
let steam2id = steamid.steam2id()?;
```

### steam64id to steam3id
```rust
# use steamid::SteamID;
let steamid = SteamID::new(76561198181797231);
let steam3id = steamid.steam3id()?;
```