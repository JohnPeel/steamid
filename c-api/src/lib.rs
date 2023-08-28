#![allow(clippy::missing_safety_doc)]

extern crate alloc;

use alloc::slice;
use core::{
    cell::RefCell,
    ffi::{c_char, c_int, CStr},
    ptr,
};
// TODO: change to `core::error::Error` when stabilized.
use std::error::Error;

pub use steamid::{
    AccountId, AccountNumber, AccountType, AuthServer, ChatFlags, Instance, RawSteamId, SteamId,
    Universe,
};

/// The expected length of the steam2id representation of a `SteamId`.
///
/// Useful for creating buffers when calling `steamid_steam2id`.
///
/// ```c
/// char steam2id[STEAM2ID_LENGTH + 1];
/// steamid_steam2id(&steamid, steam2id, STEAM2ID_LENGTH + 1);
/// ```
pub const STEAM2ID_LENGTH: usize = 18;

#[repr(C)]
#[derive(Clone, Copy)]
pub enum ExitCode {
    Success = 0,
    Error = -1,
}
const _: () =
    [(); 1][(core::mem::size_of::<ExitCode>() == core::mem::size_of::<c_int>()) as usize ^ 1];

thread_local! {
    static LAST_ERROR: RefCell<Option<Box<dyn Error + 'static>>> = RefCell::new(None);
}

pub(crate) fn update_last_error(error: impl Into<Box<dyn Error + 'static>>) {
    LAST_ERROR.with(|last_error| *last_error.borrow_mut() = Some(error.into()));
}

/// Return the string representation of the last error.
#[no_mangle]
pub unsafe extern "C" fn steamid_last_error(buffer: *mut c_char, length: c_int) -> c_int {
    if buffer.is_null() {
        return -1;
    }

    let Some(error) = LAST_ERROR.with(|last_error| last_error.borrow_mut().take()) else {
        return 0;
    };
    let error_message = error.to_string();
    let error_message = error_message.as_bytes();

    // Buffer is not large enough to fit error message and the null terminator.
    if (length as usize) < error_message.len() + 1 {
        update_last_error(error);
        return -1;
    }

    let buffer = slice::from_raw_parts_mut(buffer.cast::<u8>(), length as usize);
    let (buffer, zero_out) = buffer.split_at_mut(error_message.len());

    ptr::copy_nonoverlapping(error_message.as_ptr(), buffer.as_mut_ptr(), buffer.len());
    ptr::write_bytes(zero_out.as_mut_ptr(), 0, zero_out.len());

    error_message.len() as c_int
}

/// Constructs a new `SteamId` from a steam64id.
///
/// # Errors
/// This method will return an error if the steam64id is invalid.
#[no_mangle]
pub unsafe extern "C" fn steamid_new(id: u64, steamid: *mut SteamId) -> ExitCode {
    let Some(steamid) = steamid.as_mut() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    match SteamId::new(id) {
        Ok(id) => {
            *steamid = id;
            ExitCode::Success
        }
        Err(error) => {
            update_last_error(error);
            ExitCode::Error
        }
    }
}

/// Returns the `Universe` of the `SteamId`.
///
/// # Errors
/// This method returns an error if the universe is invalid.
#[no_mangle]
pub unsafe extern "C" fn steamid_get_universe(
    steamid: *const SteamId,
    universe: *mut Universe,
) -> ExitCode {
    let Some(steamid) = steamid.as_ref() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    let Some(universe) = universe.as_mut() else {
        update_last_error("unexpected null pointer provided for universe");
        return ExitCode::Error;
    };

    *universe = match steamid.try_universe() {
        Ok(universe) => universe,
        Err(error) => {
            update_last_error(error);
            return ExitCode::Error;
        }
    };
    ExitCode::Success
}

/// Sets the `Universe` of the `SteamId`.
#[no_mangle]
pub unsafe extern "C" fn steamid_set_universe(
    steamid: *mut SteamId,
    universe: Universe,
) -> ExitCode {
    let Some(steamid) = steamid.as_mut() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    steamid.set_universe(universe);
    ExitCode::Success
}

/// Returns the account type of the `SteamId`.
///
/// # Errors
/// This method returns an error if the account type is invalid.
#[no_mangle]
pub unsafe extern "C" fn steamid_get_account_type(
    steamid: *const SteamId,
    account_type: *mut AccountType,
) -> ExitCode {
    let Some(steamid) = steamid.as_ref() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    let Some(account_type) = account_type.as_mut() else {
        update_last_error("unexpected null pointer provided for account_type");
        return ExitCode::Error;
    };

    *account_type = match steamid.try_account_type() {
        Ok(account_type) => account_type,
        Err(error) => {
            update_last_error(error);
            return ExitCode::Error;
        }
    };
    ExitCode::Success
}

/// Sets the account type of the `SteamId`.
#[no_mangle]
pub unsafe extern "C" fn steamid_set_account_type(
    steamid: *mut SteamId,
    account_type: AccountType,
) -> ExitCode {
    let Some(steamid) = steamid.as_mut() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    steamid.set_account_type(account_type);
    ExitCode::Success
}

/// Returns the instance of the `SteamId`.
///
/// # Errors
/// This method returns an error if the instance is invalid.
#[no_mangle]
pub unsafe extern "C" fn steamid_get_instance(
    steamid: *const SteamId,
    instance: *mut Instance,
) -> ExitCode {
    let Some(steamid) = steamid.as_ref() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    let Some(instance) = instance.as_mut() else {
        update_last_error("unexpected null pointer provided for instance");
        return ExitCode::Error;
    };

    *instance = match steamid.try_instance() {
        Ok(instance) => instance,
        Err(error) => {
            update_last_error(error);
            return ExitCode::Error;
        }
    };
    ExitCode::Success
}

/// Sets the instance of the `SteamId`.
#[no_mangle]
pub unsafe extern "C" fn steamid_set_instance(
    steamid: *mut SteamId,
    instance: Instance,
) -> ExitCode {
    let Some(steamid) = steamid.as_mut() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    steamid.set_instance(instance);
    ExitCode::Success
}

/// Returns the `AccountNumber` of the `SteamId`.
///
/// # Errors
/// This method returns an error if the account number is invalid.
#[no_mangle]
pub unsafe extern "C" fn steamid_get_account_number(
    steamid: *const SteamId,
    account_number: *mut AccountNumber,
) -> ExitCode {
    let Some(steamid) = steamid.as_ref() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    let Some(account_number) = account_number.as_mut() else {
        update_last_error("unexpected null pointer provided for account_number");
        return ExitCode::Error;
    };

    *account_number = match steamid.try_account_number() {
        Ok(account_number) => account_number,
        Err(error) => {
            update_last_error(error);
            return ExitCode::Error;
        }
    };
    ExitCode::Success
}

/// Sets the `AccountNumber` of the `SteamId`.
#[no_mangle]
pub unsafe extern "C" fn steamid_set_account_number(
    steamid: *mut SteamId,
    account_number: AccountNumber,
) -> ExitCode {
    let Some(steamid) = steamid.as_mut() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    steamid.set_account_number(account_number);
    ExitCode::Success
}

/// Returns the `AccountId` of the `SteamId`.
#[no_mangle]
pub unsafe extern "C" fn steamid_get_account_id(
    steamid: *const SteamId,
    account_id: *mut AccountId,
) -> ExitCode {
    let Some(steamid) = steamid.as_ref() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    let Some(account_id) = account_id.as_mut() else {
        update_last_error("unexpected null pointer provided for account_id");
        return ExitCode::Error;
    };

    *account_id = steamid.account_id();
    ExitCode::Success
}

/// Sets the `AccountId` of the `SteamId`.
#[no_mangle]
pub unsafe extern "C" fn steamid_set_account_id(
    steamid: *mut SteamId,
    account_id: AccountId,
) -> ExitCode {
    let Some(steamid) = steamid.as_mut() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    steamid.set_account_id(account_id);
    ExitCode::Success
}

/// Returns the `AuthServer` of the `SteamId`.
#[no_mangle]
pub unsafe extern "C" fn steamid_get_auth_server(
    steamid: *const SteamId,
    auth_server: *mut AuthServer,
) -> ExitCode {
    let Some(steamid) = steamid.as_ref() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    let Some(auth_server) = auth_server.as_mut() else {
        update_last_error("unexpected null pointer provided for auth_server");
        return ExitCode::Error;
    };

    *auth_server = steamid.auth_server();
    ExitCode::Success
}

/// Sets the `AuthServer` of the `SteamId`.
#[no_mangle]
pub unsafe extern "C" fn steamid_set_auth_server(
    steamid: *mut SteamId,
    auth_server: AuthServer,
) -> ExitCode {
    let Some(steamid) = steamid.as_mut() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    steamid.set_auth_server(auth_server);
    ExitCode::Success
}

/// Generalize a steamid
///
/// # Safety
/// `steamid` must be a pointer to a valid u64 steam id.
#[no_mangle]
pub unsafe extern "C" fn steamid_generalize(steamid: *mut SteamId) -> ExitCode {
    let Some(steamid) = steamid.as_mut() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    *steamid = steamid.generalize();
    ExitCode::Success
}

/// Returns the steam2id representation of the `SteamId`.
///
/// # Errors
/// This method returns an error if the universe or account number are invalid.
#[no_mangle]
pub unsafe extern "C" fn steamid_steam2id(
    steamid: *const SteamId,
    buffer: *mut c_char,
    length: c_int,
) -> c_int {
    let Some(steamid) = steamid.as_ref() else {
        update_last_error("unexpected null pointer provided for steamid");
        return -1;
    };

    if buffer.is_null() {
        update_last_error("unexpected null pointer provided for buffer");
        return -1;
    }

    let steam2id = steamid.steam2id();
    let steam2id = steam2id.as_bytes();

    if (length as usize) < steam2id.len() + 1 {
        update_last_error("buffer too small");
        return -1;
    }

    let buffer = slice::from_raw_parts_mut(buffer.cast::<u8>(), length as usize);
    let (buffer, zero_out) = buffer.split_at_mut(steam2id.len());

    ptr::copy_nonoverlapping(steam2id.as_ptr(), buffer.as_mut_ptr(), buffer.len());
    ptr::write_bytes(zero_out.as_mut_ptr(), 0, zero_out.len());

    buffer.len() as c_int
}

/// Parse steam2id into a `SteamId`.
///
/// # Errors
/// This method returns an error if the steam2id is invalid.
///
/// # Safety
/// `steam2id` must be a proper null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn steamid_decode_steam2id(
    steam2id: *const c_char,
    steamid: *mut SteamId,
) -> ExitCode {
    if steam2id.is_null() {
        update_last_error("unexpected null pointer provided for steam2id");
        return ExitCode::Error;
    };

    let Some(steamid) = steamid.as_mut() else {
        update_last_error("unexpected null pointer provided for steamid");
        return ExitCode::Error;
    };

    let steam2id = CStr::from_ptr(steam2id);

    let steam2id = match steam2id.to_str() {
        Ok(steam2id) => steam2id,
        Err(error) => {
            update_last_error(error);
            return ExitCode::Error;
        }
    };

    *steamid = match SteamId::parse_steam2id(steam2id, None, None) {
        Ok(steamid) => steamid,
        Err(error) => {
            update_last_error(error);
            return ExitCode::Error;
        }
    };

    ExitCode::Success
}

#[cfg(test)]
mod tests {
    use inline_c::assert_c;

    #[test]
    fn decode_steam2id() {
        let assert = assert_c! {
            #include <string.h>
            #include <assert.h>

            #include "steamid.h"

            int main() {
                SteamId steamid = 0;
                char steam2id[] = "STEAM_1:1:19461996";

                assert(steamid_decode_steam2id(steam2id, &steamid) == ExitCode_Success);
                assert(steamid == 76561197999189721);

                SteamId other_steamid = steamid;
                assert(steamid_set_universe(&other_steamid, Universe_Invalid) == ExitCode_Success);
                assert(steamid != other_steamid);

                char other_steam2id[STEAM2ID_LENGTH + 1];
                assert(steamid_steam2id(&other_steamid, other_steam2id, STEAM2ID_LENGTH + 1) == STEAM2ID_LENGTH);
                assert(strncmp("STEAM_0:1:19461996", other_steam2id, STEAM2ID_LENGTH) == 0);

                assert(steamid_generalize(&steamid) == ExitCode_Success);
                assert(steamid_generalize(&other_steamid) == ExitCode_Success);
                assert(steamid == other_steamid);

                return 0;
            }
        }
        .assert();

        let output = assert.get_output();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);

        assert_eq!(&stdout, "");
        assert_eq!(
            &stderr, "",
            "\n\n\n======= STDERR =======\n\n{}\n======================\n\n\n",
            stderr
        );
        assert_eq!(output.status.to_string().as_str(), "exit status: 0");
    }
}
