# Steam ID type and accessories

This project provides the `SteamId` type with conversion methods to convert between different Steam Id formats.

Hosted on [GitHub](https://github.com/JohnPeel/steamid-rs).

## Examples and Usage

### Initialize from steam64id
```rust
use steamid::{SteamId, Error};

fn main() -> Result<(), Error> {
    let steamid = SteamId::new(76561198181797231)?;
    
    Ok(())
}
```

### Parse a steam2id
```rust
use steamid::{SteamId, AccountType, Instance, Error};

fn main() -> Result<(), Error> {
    let steamid = SteamId::parse_steam2id("STEAM_0:0:12345", None, None)?;

    // We can also specify the account type and instance (these are the defaults)
    let steamid = SteamId::parse_steam2id("STEAM_0:0:12345", AccountType::Individual, Instance::Desktop)?;
    
    Ok(())
}
```

### Parse a steam3id
```rust
use steamid::{SteamId, Instance, Error};

fn main() -> Result<(), Error> {
    let steamid = SteamId::parse_steam3id("[U:1:12345]", None)?;
    
    Ok(())
}
```

### Convert steam64id to steam2id
```rust
use steamid::{SteamId, Error};

fn main() -> Result<(), Error> {
    let steamid = SteamId::new(76561198181797231)?;
    let steam2id = steamid.steam2id();

    Ok(())
}
```

### Convert steam64id to steam3id
```rust
use steamid::{SteamId, Error};

fn main() -> Result<(), Error> {
    let steamid = SteamId::new(76561198181797231)?;
    let steam3id = steamid.steam3id();

    Ok(())
}
```

### Convert steam64id to Community Link
```rust
use steamid::{SteamId, Error};

fn main() -> Result<(), Error> {
    let steamid = SteamId::new(4503603961261785)?;
    let community_link = steamid.community_link();

    Ok(())
}
```
