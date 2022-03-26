import uuidv4 from "uuid/v4";
import express from "express";
import { Request, Response } from "express";
import path from "path";
import crypto from "crypto"
import {
  AbsoluteCoord,
  NormalMove,
  InfAfterStep,
  AfterHalfAcceptance,
  Ciurl,
  RetInfAfterStep,
  RetNormalMove,
  RetAfterHalfAcceptance,
  RetRandomEntry,
  RetRandomPoll,
  RetRandomCancel,
  RetMainPoll,
  SrcDst,
  SrcStepDstFinite,
  MoveToBePolled,
  Color, Profession, RetTyMok, RetTaXot, WhoGoesFirst, RetWhetherTyMokPoll, RetInfPoll, RetVsCpuEntry,
  RetFriendPoll, RetFriendDeleteRoom, RetFriendMakeRoom, RetFriendJoinRoom
} from "cerke_online_api";

import { Hand, ObtainablePieces, calculate_hands_and_score_from_pieces } from "cerke_hands_and_score";
import * as t from "io-ts";
import { pipe } from "fp-ts/lib/pipeable";
import { fold } from "fp-ts/lib/Either";
import { generateBotMove } from "./bot";
import {
  Field, Tuple4,
  Piece, NonTam2Piece, NonTam2PieceIAOwner, NonTam2PieceNonIAOwner, Side, Board
} from "./type_gamestate";
import { Season, Log2_Rate } from "cerke_online_api"
import { create_initialized_board } from "./create_initialized_board";

// For the notifier. I don't think it should live in index.ts, but for now let's just do it
import Discord from "discord.js";

const publicly_announce_matching = (() => {
  if (process.env.PUBLIC_ANNOUNCEMENT === "DISCORD") {
    const client = new Discord.Client();
    client.once('ready', () => {
      // channel #バックエンド起動ログ
      (client.channels.cache.get('900419722313601114')! as Discord.TextChannel).send('cerke online discord notifier is Ready!')
    });

    client.login(process.env.DISCORD_NOTIFIER_TOKEN);

    return (msg: string, is_staging: boolean) => {
      if (is_staging) {
        // channel #デバッグ環境マッチングログ
        (client.channels.cache.get('902952289378115625')! as Discord.TextChannel).send(msg)

      } else {
        // channel #本番環境マッチングログ
        (client.channels.cache.get('900417626243731537')! as Discord.TextChannel).send(msg)
      }
    };
  }
  return (_msg: string, _is_staging: boolean) => { };
})();


type RoomId = string & { __RoomIdBrand: never };
type RoomKey = string & { __RoomKeyBrand: never };
type SessionToken = string & { __SessionTokenBrand: never };
type BotToken = string & { __BotTokenBrand: never };

type RoomInfoWithPerspective = {
  room_id: RoomId;
  is_first_move_my_move: Tuple4<WhoGoesFirst>;
  is_IA_down_for_me: boolean;
};

interface GameState {
  f: Field;
  tam_itself_is_tam_hue: boolean;
  is_IA_owner_s_turn: boolean;
  waiting_for_after_half_acceptance: null | {
    src: AbsoluteCoord;
    step: AbsoluteCoord;
  };
  season: Season;
  IA_owner_s_score: number;
  log2_rate: Log2_Rate;
  moves_to_be_polled: Tuple4<Array<MovePiece>>;
}


type HandCompletionStatus = null | "ty mok1" | "ta xot1" | "not yet";

type MovePiece = {
  move: MoveToBePolled;
  status: HandCompletionStatus;
  byIAOwner: boolean;
};

const ColorVerifier = t.union([t.literal(0), t.literal(1)]);
const ProfessionVerifier = t.union([
  t.literal(0),
  t.literal(1),
  t.literal(2),
  t.literal(3),
  t.literal(4),
  t.literal(5),
  t.literal(6),
  t.literal(7),
  t.literal(8),
  t.literal(9),
]);

const AbsoluteRowVerifier = t.union([
  t.literal("A"),
  t.literal("E"),
  t.literal("I"),
  t.literal("U"),
  t.literal("O"),
  t.literal("Y"),
  t.literal("AI"),
  t.literal("AU"),
  t.literal("IA"),
]);

const AbsoluteColumnVerifier = t.union([
  t.literal("K"),
  t.literal("L"),
  t.literal("N"),
  t.literal("T"),
  t.literal("Z"),
  t.literal("X"),
  t.literal("C"),
  t.literal("M"),
  t.literal("P"),
]);

const AbsoluteCoordVerifier = t.tuple([
  AbsoluteRowVerifier,
  AbsoluteColumnVerifier,
]);

const InfAfterStepVerifier = t.strict({
  type: t.literal("InfAfterStep"),
  src: AbsoluteCoordVerifier,
  step: AbsoluteCoordVerifier,
  plannedDirection: AbsoluteCoordVerifier,
});

const AfterHalfAcceptanceVerifier = t.strict({
  type: t.literal("AfterHalfAcceptance"),
  dest: t.union([AbsoluteCoordVerifier, t.null]),
});

const NormalNonTamMoveVerifier = t.strict({
  type: t.literal("NonTamMove"),
  data: t.union([
    t.strict({
      type: t.literal("FromHand"),
      color: ColorVerifier,
      prof: ProfessionVerifier,
      dest: AbsoluteCoordVerifier,
    }),
    t.strict({
      type: t.literal("SrcDst"),
      src: AbsoluteCoordVerifier,
      dest: AbsoluteCoordVerifier,
    }),
    t.strict({
      type: t.literal("SrcStepDstFinite"),
      src: AbsoluteCoordVerifier,
      step: AbsoluteCoordVerifier,
      dest: AbsoluteCoordVerifier,
    }),
  ]),
});

const TamMoveVerifier = t.union([
  t.strict({
    type: t.literal("TamMove"),
    stepStyle: t.literal("NoStep"),
    src: AbsoluteCoordVerifier,
    firstDest: AbsoluteCoordVerifier,
    secondDest: AbsoluteCoordVerifier,
  }),
  t.strict({
    type: t.literal("TamMove"),
    stepStyle: t.union([
      t.literal("StepsDuringFormer"),
      t.literal("StepsDuringLatter"),
    ]),
    src: AbsoluteCoordVerifier,
    step: AbsoluteCoordVerifier,
    firstDest: AbsoluteCoordVerifier,
    secondDest: AbsoluteCoordVerifier,
  }),
]);

const NormalMoveVerifier = t.union([
  NormalNonTamMoveVerifier,
  TamMoveVerifier,
]);

const PORT = process.env.PORT || 23564;
const bodyParser = require("body-parser");
const sha256_first7 = (str: string) => crypto.createHash('sha256').update(str, 'utf8').digest('hex').slice(0, 7);

const { getPiece, setPiece } = (() => {
  function fromAbsoluteCoord_([absrow, abscol]: AbsoluteCoord): [
    number,
    number,
  ] {
    let rowind: number;

    if (absrow === "A") {
      rowind = 0;
    } else if (absrow === "E") {
      rowind = 1;
    } else if (absrow === "I") {
      rowind = 2;
    } else if (absrow === "U") {
      rowind = 3;
    } else if (absrow === "O") {
      rowind = 4;
    } else if (absrow === "Y") {
      rowind = 5;
    } else if (absrow === "AI") {
      rowind = 6;
    } else if (absrow === "AU") {
      rowind = 7;
    } else if (absrow === "IA") {
      rowind = 8;
    } else {
      const _should_not_reach_here: never = absrow;
      throw new Error("does not happen");
    }

    let colind: number;

    if (abscol === "K") {
      colind = 0;
    } else if (abscol === "L") {
      colind = 1;
    } else if (abscol === "N") {
      colind = 2;
    } else if (abscol === "T") {
      colind = 3;
    } else if (abscol === "Z") {
      colind = 4;
    } else if (abscol === "X") {
      colind = 5;
    } else if (abscol === "C") {
      colind = 6;
    } else if (abscol === "M") {
      colind = 7;
    } else if (abscol === "P") {
      colind = 8;
    } else {
      const _should_not_reach_here: never = abscol;
      throw new Error("does not happen");
    }

    if (true) {
      return [rowind, colind];
    }
  }

  function getPiece(game_state: Readonly<GameState>, coord: AbsoluteCoord) {
    const [i, j] = fromAbsoluteCoord_(coord);
    return game_state.f.currentBoard[i][j];
  }

  function setPiece(
    game_state: GameState,
    coord: AbsoluteCoord,
    piece: Piece | null,
  ): Piece | null {
    const [i, j] = fromAbsoluteCoord_(coord);
    const originally_occupied_by = game_state.f.currentBoard[i][j];
    game_state.f.currentBoard[i][j] = piece;
    return originally_occupied_by;
  }
  return { getPiece, setPiece };
})();

function isNonTam2PieceIAOwner(piece: Piece): piece is NonTam2PieceIAOwner {
  if (piece === "Tam2") {
    return false;
  }
  if (piece.side === Side.IAOwner) {
    return true;
  }
  return false;
}

function isNonTam2PieceNonIAOwner(
  piece: Piece,
): piece is NonTam2PieceNonIAOwner {
  if (piece === "Tam2") {
    return false;
  }
  if (piece.side === Side.NonIAOwner) {
    return true;
  }
  return false;
}

function addToHop1Zuo1OfIAOwner(
  game_state: GameState,
  piece: NonTam2PieceNonIAOwner,
) {
  const flipped: NonTam2PieceIAOwner = {
    prof: piece.prof,
    color: piece.color,
    side: Side.IAOwner,
  };
  game_state.f.hop1zuo1OfIAOwner.push(flipped);
}

function addToHop1Zuo1OfNonIAOwner(
  game_state: GameState,
  piece: NonTam2PieceIAOwner,
) {
  const flipped: NonTam2PieceNonIAOwner = {
    prof: piece.prof,
    color: piece.color,
    side: Side.NonIAOwner,
  };
  game_state.f.hop1zuo1OfNonIAOwner.push(flipped);
}

function removeFromHop1Zuo1OfIAOwner(
  game_state: GameState,
  color: Color,
  prof: Profession,
): NonTam2PieceIAOwner {
  const ind = game_state.f.hop1zuo1OfIAOwner.findIndex(
    p => p.color === color && p.prof === prof,
  );
  if (ind === -1) {
    throw new Error("What should exist in the hand does not exist");
  }
  const [removed] = game_state.f.hop1zuo1OfIAOwner.splice(ind, 1);
  return removed;
}

function removeFromHop1Zuo1OfNonIAOwner(
  game_state: GameState,
  color: Color,
  prof: Profession,
): NonTam2PieceNonIAOwner {
  const ind = game_state.f.hop1zuo1OfNonIAOwner.findIndex(
    p => p.color === color && p.prof === prof,
  );
  if (ind === -1) {
    throw new Error("What should exist in the hand does not exist");
  }
  const [removed] = game_state.f.hop1zuo1OfNonIAOwner.splice(ind, 1);
  return removed;
}

function isWater([row, col]: AbsoluteCoord): boolean {
  return (
    (row === "O" && col === "N") ||
    (row === "O" && col === "T") ||
    (row === "O" && col === "Z") ||
    (row === "O" && col === "X") ||
    (row === "O" && col === "C") ||
    (row === "I" && col === "Z") ||
    (row === "U" && col === "Z") ||
    (row === "Y" && col === "Z") ||
    (row === "AI" && col === "Z")
  );
}

function isInfAfterStep(a: {
  byIAOwner: boolean;
  status: HandCompletionStatus;
  move: MoveToBePolled;
}): a is {
  byIAOwner: boolean;
  status: HandCompletionStatus;
  move: {
    type: "InfAfterStep";
    src: AbsoluteCoord;
    step: AbsoluteCoord;
    plannedDirection: AbsoluteCoord;
    stepping_ciurl: Ciurl;
    finalResult: null /* not yet known */ | {
      dest: AbsoluteCoord;
      water_entry_ciurl?: Ciurl;
      thwarted_by_failing_water_entry_ciurl: Ciurl | null
    };
  };
} {
  if (a.move.type === "NonTamMove") {
    return false;
  } else if (a.move.type === "TamMove") {
    return false;
  } else if (a.move.type === "InfAfterStep") {
    return true;
  } else {
    const _should_not_reach_here: never = a.move;
    throw new Error("should not happen");
  }
}

function getLastMove(game_state: Readonly<GameState>) {
  const arr = game_state.moves_to_be_polled[game_state.season];
  if (arr.length === 0) {
    return undefined;
  }
  return arr[arr.length - 1];
}

function howManyDaysHavePassed(game_state: Readonly<GameState>): number {
  const arr = game_state.moves_to_be_polled[game_state.season];
  return arr.length;
}

function ifStepTamEditScore(
  game_state: GameState,
  step: AbsoluteCoord,
  room_info: RoomInfoWithPerspective,
) {
  if (getPiece(game_state, step) === "Tam2") {
    if (room_info.is_IA_down_for_me) {
      game_state.IA_owner_s_score += -5 * Math.pow(2, game_state.log2_rate);
      if (game_state.IA_owner_s_score >= 40) {
        console.log("the game has ended!"); // FIXME
      }
    } else {
      game_state.IA_owner_s_score -= -5 * Math.pow(2, game_state.log2_rate);
      if (game_state.IA_owner_s_score < 0) {
        console.log("the game has ended!"); // FIXME
      }
    }
  }
}

function analyzeAfterHalfAcceptanceAndUpdate(
  msg: AfterHalfAcceptance,
  room_info: RoomInfoWithPerspective,
): RetAfterHalfAcceptance {
  const game_state = room_to_gamestate.get(room_info.room_id)!;
  const { src, step } = game_state.waiting_for_after_half_acceptance!;
  if (msg.dest == null) {
    // The player intends to pass, possibly because of dissatisfaction against the stepping_ciurl
    const obj = getLastMove(game_state);
    if (typeof obj === "undefined") {
      return { type: "Err", why_illegal: "there was no last move" };
    }

    if (!isInfAfterStep(obj)) {
      return { type: "Err", why_illegal: "the last move was not InfAfterStep" };
    }

    obj.move.finalResult = {
      dest: src,
      thwarted_by_failing_water_entry_ciurl: null // The player intends to pass. It was not thwarted by failing water_entry_ciurl.
    };

    ifStepTamEditScore(game_state, step, room_info);
    // hasn't actually moved, so the water entry cannot fail
    return { type: "WithoutWaterEntry" };
  }

  const piece = getPiece(game_state, src);

  if (piece === null) {
    throw new Error(`While handling analyzeAfterHalfAcceptanceAndUpdate, expected to find a piece at position ${JSON.stringify(src)}, but did not find it; the game's state was ${JSON.stringify(game_state)}`);
  }

  game_state.waiting_for_after_half_acceptance = null;

  if (isWater(src) || (piece !== "Tam2" && piece.prof === Profession.Nuak1)) {
    const {
      hand_is_made,
    } = movePieceFromSrcToDestWhileTakingOpponentPieceIfNeeded(
      game_state,
      src,
      msg.dest,
      room_info.is_IA_down_for_me,
    );
    const final_obj = getLastMove(game_state);
    if (typeof final_obj === "undefined" || !isInfAfterStep(final_obj)) {
      return { type: "Err", why_illegal: "the last move was not InfAfterStep" };
    }

    final_obj.move.finalResult = {
      dest: msg.dest,
      thwarted_by_failing_water_entry_ciurl: null /* The src is water, or the profession is Nuak1; hence it is impossible that the move was thwarted by the failure of water_entry_ciurl */
    };

    final_obj.status = hand_is_made ? "not yet" : null;

    const ans: RetAfterHalfAcceptance = {
      type: "WithoutWaterEntry",
    };

    ifStepTamEditScore(game_state, step, room_info);
    return ans;
  }

  if (isWater(msg.dest)) {
    const water_entry_ciurl: Ciurl = [
      Math.random() < 0.5,
      Math.random() < 0.5,
      Math.random() < 0.5,
      Math.random() < 0.5,
      Math.random() < 0.5,
    ];

    const obj = getLastMove(game_state);
    if (typeof obj === "undefined" || !isInfAfterStep(obj)) {
      return { type: "Err", why_illegal: "the last move was not InfAfterStep" };
    }

    if (water_entry_ciurl.filter(a => a).length >= 3) {
      const {
        hand_is_made,
      } = movePieceFromSrcToDestWhileTakingOpponentPieceIfNeeded(
        game_state,
        src,
        msg.dest,
        room_info.is_IA_down_for_me,
      );
      obj.move.finalResult = {
        dest: msg.dest,
        water_entry_ciurl,
        thwarted_by_failing_water_entry_ciurl: null /* water entry is successful. Hence it is not thwarted. */
      };
      if (hand_is_made) {
        obj.status = "not yet";
      }
    } else {
      obj.move.finalResult = {
        dest: src, // failed; returning to the original
        // NO WATER ENTRY CIURL IF RETURNING TO THE ORIGINAL
        thwarted_by_failing_water_entry_ciurl: water_entry_ciurl // it IS thwarted by failing water_entry_ciurl
      };
      obj.status = null;
    }

    const ans: RetAfterHalfAcceptance = {
      type: "WithWaterEntry",
      ciurl: water_entry_ciurl,
    };

    ifStepTamEditScore(game_state, step, room_info);
    return ans;
  } else { // the destination is not water
    const {
      hand_is_made,
    } = movePieceFromSrcToDestWhileTakingOpponentPieceIfNeeded(
      game_state,
      src,
      msg.dest,
      room_info.is_IA_down_for_me,
    );

    const obj = getLastMove(game_state);
    if (typeof obj === "undefined" || !isInfAfterStep(obj)) {
      return { type: "Err", why_illegal: "the last move was not InfAfterStep" };
    }

    obj.move.finalResult = {
      dest: msg.dest,
      thwarted_by_failing_water_entry_ciurl: null /* not thwarted: the destination is not water */
    };

    if (hand_is_made) {
      obj.status = "not yet";
    }

    const ans: RetAfterHalfAcceptance = {
      type: "WithoutWaterEntry"
    };

    ifStepTamEditScore(game_state, step, room_info);
    return ans;
  }
}

function analyzeValidInfAfterStepMessageAndUpdate(
  msg: InfAfterStep,
  room_info: RoomInfoWithPerspective,
): RetInfAfterStep {
  const game_state = room_to_gamestate.get(room_info.room_id)!;
  game_state.waiting_for_after_half_acceptance = {
    src: msg.src,
    step: msg.step,
  };

  const stepping_ciurl: Ciurl = [
    Math.random() < 0.5,
    Math.random() < 0.5,
    Math.random() < 0.5,
    Math.random() < 0.5,
    Math.random() < 0.5,
  ];
  game_state.moves_to_be_polled[game_state.season].push({
    byIAOwner: room_info.is_IA_down_for_me,
    move: {
      type: msg.type,
      src: msg.src,
      step: msg.step,
      plannedDirection: msg.plannedDirection,
      stepping_ciurl,
      finalResult: null,
    },
    status: null /* no piece has been taken yet */,
  });
  const ans: RetInfAfterStep = {
    type: "Ok",
    ciurl: stepping_ciurl,
  };
  return ans;
}

function calculateHandsAndScore(pieces: NonTam2Piece[]) {
  const hop1zuo1: ObtainablePieces[] = pieces.map(p =>
    toObtainablePiece(p.color, p.prof),
  );
  const res:
    | { error: false; score: number; hands: Hand[] }
    | {
      error: true;
      too_many: ObtainablePieces[];
    } = calculate_hands_and_score_from_pieces(hop1zuo1);
  if (res.error === true) {
    throw new Error(`should not happen: too many of ${res.too_many.join(",")}`);
  }

  return { hands: res.hands, score: res.score };
}

function toObtainablePiece(color: Color, prof: Profession): ObtainablePieces {
  const a: ObtainablePieces[][] = [
    [
      "赤船",
      "赤兵",
      "赤弓",
      "赤車",
      "赤虎",
      "赤馬",
      "赤筆",
      "赤巫",
      "赤将",
      "赤王",
    ],
    [
      "黒船",
      "黒兵",
      "黒弓",
      "黒車",
      "黒虎",
      "黒馬",
      "黒筆",
      "黒巫",
      "黒将",
      "黒王",
    ],
  ];
  return a[color][prof];
}

function movePieceFromSrcToDestWhileTakingOpponentPieceIfNeeded(
  game_state: GameState,
  src: AbsoluteCoord,
  dest: AbsoluteCoord,
  is_IA_down_for_me: boolean,
): { hand_is_made: boolean } {
  const piece = setPiece(game_state, src, null)!;
  const maybe_taken = setPiece(game_state, dest, piece);
  if (maybe_taken != null) {
    if (is_IA_down_for_me) {
      if (!isNonTam2PieceNonIAOwner(maybe_taken)) {
        throw new Error("tried to take either an ally or tam2");
      }
      const old_state = calculateHandsAndScore(game_state.f.hop1zuo1OfIAOwner);
      addToHop1Zuo1OfIAOwner(game_state, maybe_taken);
      const new_state = calculateHandsAndScore(game_state.f.hop1zuo1OfIAOwner);
      return { hand_is_made: new_state.score !== old_state.score };
    } else {
      if (!isNonTam2PieceIAOwner(maybe_taken)) {
        throw new Error("tried to take either an ally or tam2");
      }
      const old_state = calculateHandsAndScore(
        game_state.f.hop1zuo1OfNonIAOwner,
      );
      addToHop1Zuo1OfNonIAOwner(game_state, maybe_taken);
      const new_state = calculateHandsAndScore(
        game_state.f.hop1zuo1OfNonIAOwner,
      );
      return { hand_is_made: new_state.score !== old_state.score };
    }
  }
  return { hand_is_made: false };
}

function replyToWhetherTyMokPoll(
  room_info: RoomInfoWithPerspective,
): RetWhetherTyMokPoll {
  const game_state = room_to_gamestate.get(room_info.room_id)!;

  /* needs to access the current or previous season */
  const arr: MovePiece[] = (() => {
    if (game_state.season === 0) {
      return game_state.moves_to_be_polled[game_state.season];
    }
    if (game_state.moves_to_be_polled[game_state.season].length === 0) {
      // the season has already progressed
      return game_state.moves_to_be_polled[game_state.season - 1];
    } else {
      // not yet progressed
      return game_state.moves_to_be_polled[game_state.season];
    }
  })();

  if (arr.length === 0) {
    return { type: "Err", why_illegal: "no last move" };
  }

  const dat = arr[arr.length - 1];

  if (dat.status == null) {
    return { type: "Err", why_illegal: "apparently, no hand was made" };
  } else if (dat.status === "ty mok1") {
    return { type: "TyMok" };
  } else if (dat.status === "not yet") {
    return { type: "NotYetDetermined" };
  } else if (dat.status === "ta xot1") {
    return { type: "TaXot", is_first_move_my_move: room_info.is_first_move_my_move[game_state.season] };
  } else {
    const _should_not_reach_here: never = dat.status;
    throw new Error("should not happen");
  }
}

function replyToInfPoll(room_info: RoomInfoWithPerspective): RetInfPoll {
  const game_state = room_to_gamestate.get(room_info.room_id)!;

  const dat = getLastMove(game_state);
  if (typeof dat === "undefined") {
    return { type: "Err", why_illegal: "there is no last move" };
  }

  if (room_info.is_IA_down_for_me === dat.byIAOwner) {
    return { type: "Err", why_illegal: "it's not your turn" };
  }

  if (dat.move.type !== "InfAfterStep") {
    return { type: "Err", why_illegal: "InfAfterStep is not happening" };
  }

  if (dat.move.finalResult == null) {
    return { type: "NotYetDetermined" };
  }

  return { type: "MoveMade", content: dat.move };
}

function replyToMainPoll(room_info: RoomInfoWithPerspective): RetMainPoll {
  const game_state = room_to_gamestate.get(room_info.room_id)!;
  const mov = getLastMove(game_state);

  // If the last move is not played by the player, just return what we have.
  if (typeof mov !== "undefined" && room_info.is_IA_down_for_me !== mov.byIAOwner) {
    return { type: "MoveMade", content: mov.move };
  }

  // If the player is not playing against a bot, then I simply say "not yet".
  if (!room_to_bot.get(room_info.room_id)) {
    return { type: "NotYetDetermined" };
  }

  // If the player *is* playing against a bot,
  // then the reply should always be that the bot has played.
  // Hence, here I should:

  // 0. Check whether the opponent has moved tam
  const opponent_has_just_moved_tam = (() => {
    if (typeof mov === "undefined") return false;
    return mov.move.type === "TamMove";
  })();

  // 1. Generate the bot's move on the fly
  const { tactics, bot_move } = generateBotMove(game_state, howManyDaysHavePassed(game_state), opponent_has_just_moved_tam, room_info.is_IA_down_for_me);


  // 2. Update the `game_state` depending on the move I just generated.
  // To do this without duplicating the code, I just have to play one move in the bot's perspective.
  const bot_perspective: RoomInfoWithPerspective = {
    room_id: room_info.room_id,
    is_first_move_my_move: [
      swap_who_goes_first(room_info.is_first_move_my_move[0]),
      swap_who_goes_first(room_info.is_first_move_my_move[1]),
      swap_who_goes_first(room_info.is_first_move_my_move[2]),
      swap_who_goes_first(room_info.is_first_move_my_move[3]),
    ],
    is_IA_down_for_me: !room_info.is_IA_down_for_me,
  };
  const ret = analyzeValidMainMessageAndUpdate(bot_move.dat, bot_perspective);

  if (bot_move.t === "inf") {
    const ret2 = ret as RetInfAfterStep;
    if (ret2.type === "Err") { throw new Error("bot died while handling InfAfterStep!") }
    const next_move = bot_move.after[ret2.ciurl.filter(a => a).length];
    analyzeAfterHalfAcceptanceMessageAndUpdate(next_move, bot_perspective);
  }

  // 3. Send back the move I just made
  const mov2 = getLastMove(game_state);
  if (typeof mov2 === "undefined") { throw new Error("Although the bot is supposed to have played something, I cannot locate it") }

  if (mov2.status === "not yet") {
    // The bot is not yet smart enough to give ty mok1
    receiveTaXotAndUpdate(bot_perspective)
  }

  return { type: "MoveMade", message: tactics, content: mov2.move };
}

function analyzeValidNormalMoveMessageAndUpdate(
  msg: NormalMove,
  room_info: RoomInfoWithPerspective,
): RetNormalMove {
  const game_state = room_to_gamestate.get(room_info.room_id)!;
  if (msg.type === "NonTamMove") {
    if (msg.data.type === "FromHand") {
      if (room_info.is_IA_down_for_me) {
        const removed = removeFromHop1Zuo1OfIAOwner(
          game_state,
          msg.data.color,
          msg.data.prof,
        );
        const maybe_taken = setPiece(game_state, msg.data.dest, removed);
        if (maybe_taken != null) {
          throw new Error(
            "should not happen: already occupied and cannot be placed from hop1 zuo1",
          );
        }
      } else {
        const removed = removeFromHop1Zuo1OfNonIAOwner(
          game_state,
          msg.data.color,
          msg.data.prof,
        );
        const maybe_taken = setPiece(game_state, msg.data.dest, removed);
        if (maybe_taken != null) {
          throw new Error(
            "should not happen: already occupied and cannot be placed from hop1 zuo1",
          );
        }
      }

      game_state.moves_to_be_polled[game_state.season].push({
        byIAOwner: room_info.is_IA_down_for_me,
        move: {
          type: "NonTamMove",
          data: msg.data,
        },
        status: null, // never completes a new hand
      });

      // never fails
      return {
        type: "WithoutWaterEntry"
      };
    }

    const piece = getPiece(game_state, msg.data.src)!;

    if (
      isWater(msg.data.src) ||
      (piece !== "Tam2" && piece.prof === Profession.Nuak1)
    ) {
      const {
        hand_is_made,
      } = movePieceFromSrcToDestWhileTakingOpponentPieceIfNeeded(
        game_state,
        msg.data.src,
        msg.data.dest,
        room_info.is_IA_down_for_me,
      );
      game_state.moves_to_be_polled[game_state.season].push({
        byIAOwner: room_info.is_IA_down_for_me,
        move: {
          type: "NonTamMove",
          data: msg.data,
        },
        status: hand_is_made ? "not yet" : null,
      });
      // never fails
      return {
        type: "WithoutWaterEntry"
      };
    }

    if (isWater(msg.data.dest)) {
      const ciurl: Ciurl = [
        Math.random() < 0.5,
        Math.random() < 0.5,
        Math.random() < 0.5,
        Math.random() < 0.5,
        Math.random() < 0.5,
      ];

      const data: SrcDst | SrcStepDstFinite = (() => {
        if (msg.data.type === "SrcDst") {
          const ans: SrcDst = {
            type: msg.data.type,
            src: msg.data.src,
            dest: msg.data.dest,
            water_entry_ciurl: ciurl,
          };
          return ans;
        } else if (msg.data.type === "SrcStepDstFinite") {
          ifStepTamEditScore(game_state, msg.data.step, room_info);
          const ans: SrcStepDstFinite = {
            type: msg.data.type,
            src: msg.data.src,
            step: msg.data.step,
            dest: msg.data.dest,
            water_entry_ciurl: ciurl,
          };
          return ans;
        } else {
          const _should_not_reach_here: never = msg.data;
          throw new Error("should not happen");
        }
      })();

      if (ciurl.filter(a => a).length >= 3) {
        const {
          hand_is_made,
        } = movePieceFromSrcToDestWhileTakingOpponentPieceIfNeeded(
          game_state,
          msg.data.src,
          msg.data.dest,
          room_info.is_IA_down_for_me,
        );
        game_state.moves_to_be_polled[game_state.season].push({
          byIAOwner: room_info.is_IA_down_for_me,
          move: { type: "NonTamMove", data },
          status: hand_is_made ? "not yet" : null,
        });
      } else {
        game_state.moves_to_be_polled[game_state.season].push({
          byIAOwner: room_info.is_IA_down_for_me,
          move: { type: "NonTamMove", data },
          status: null, // never completes a move
        });
      }
      const ans: RetNormalMove = { type: "WithWaterEntry", ciurl };
      return ans;
    } else {
      const {
        hand_is_made,
      } = movePieceFromSrcToDestWhileTakingOpponentPieceIfNeeded(
        game_state,
        msg.data.src,
        msg.data.dest,
        room_info.is_IA_down_for_me,
      );

      game_state.moves_to_be_polled[game_state.season].push({
        byIAOwner: room_info.is_IA_down_for_me,
        move: {
          type: "NonTamMove",
          data: msg.data,
        },
        status: hand_is_made ? "not yet" : null,
      });

      const ans: RetNormalMove = {
        type: "WithoutWaterEntry"
      };
      return ans;
    }
  } else if (msg.type === "TamMove") {
    setPiece(game_state, msg.src, null);
    setPiece(game_state, msg.secondDest, "Tam2");
    // tam2 can't take

    game_state.moves_to_be_polled[game_state.season].push({
      byIAOwner: room_info.is_IA_down_for_me,
      move: msg,
      status: null, // never completes a hand
    });

    // Tam2 never fails water entry
    const ans: RetNormalMove = {
      type: "WithoutWaterEntry"
    };
    return ans;
  } else {
    let _should_not_reach_here: never = msg;
    throw new Error("should not reach here");
  }
}

function analyzeValidMainMessageAndUpdate(
  msg: InfAfterStep | NormalMove,
  room_info: RoomInfoWithPerspective,
): RetInfAfterStep | RetNormalMove {
  const game_state = room_to_gamestate.get(room_info.room_id)!;
  if (msg.type === "InfAfterStep") {
    /* InfAfterStep */
    return analyzeValidInfAfterStepMessageAndUpdate(msg, room_info);
  } else if (msg.type === "NonTamMove") {
    if (msg.data.type === "FromHand") {
      if (room_info.is_IA_down_for_me) {
        const removed = removeFromHop1Zuo1OfIAOwner(
          game_state,
          msg.data.color,
          msg.data.prof,
        );
        const maybe_taken = setPiece(game_state, msg.data.dest, removed);
        if (maybe_taken != null) {
          throw new Error(
            "should not happen: already occupied and cannot be placed from hop1 zuo1",
          );
        }
      } else {
        const removed = removeFromHop1Zuo1OfNonIAOwner(
          game_state,
          msg.data.color,
          msg.data.prof,
        );
        const maybe_taken = setPiece(game_state, msg.data.dest, removed);
        if (maybe_taken != null) {
          throw new Error(
            "should not happen: already occupied and cannot be placed from hop1 zuo1",
          );
        }
      }

      game_state.moves_to_be_polled[game_state.season].push({
        byIAOwner: room_info.is_IA_down_for_me,
        move: {
          type: "NonTamMove",
          data: msg.data,
        },
        status: null, // never completes a new hand
      });

      // never fails
      return {
        type: "WithoutWaterEntry"
      };
    }

    const piece = getPiece(game_state, msg.data.src)!;

    if (
      isWater(msg.data.src) ||
      (piece !== "Tam2" && piece.prof === Profession.Nuak1)
    ) {
      const {
        hand_is_made,
      } = movePieceFromSrcToDestWhileTakingOpponentPieceIfNeeded(
        game_state,
        msg.data.src,
        msg.data.dest,
        room_info.is_IA_down_for_me,
      );
      game_state.moves_to_be_polled[game_state.season].push({
        byIAOwner: room_info.is_IA_down_for_me,
        move: {
          type: "NonTamMove",
          data: msg.data,
        },
        status: hand_is_made ? "not yet" : null,
      });
      // never fails
      return {
        type: "WithoutWaterEntry"
      };
    }

    if (isWater(msg.data.dest)) {
      const ciurl: Ciurl = [
        Math.random() < 0.5,
        Math.random() < 0.5,
        Math.random() < 0.5,
        Math.random() < 0.5,
        Math.random() < 0.5,
      ];

      const data: SrcDst | SrcStepDstFinite = (() => {
        if (msg.data.type === "SrcDst") {
          const ans: SrcDst = {
            type: msg.data.type,
            src: msg.data.src,
            dest: msg.data.dest,
            water_entry_ciurl: ciurl,
          };
          return ans;
        } else if (msg.data.type === "SrcStepDstFinite") {
          ifStepTamEditScore(game_state, msg.data.step, room_info);
          const ans: SrcStepDstFinite = {
            type: msg.data.type,
            src: msg.data.src,
            step: msg.data.step,
            dest: msg.data.dest,
            water_entry_ciurl: ciurl,
          };
          return ans;
        } else {
          const _should_not_reach_here: never = msg.data;
          throw new Error("should not happen");
        }
      })();

      if (ciurl.filter(a => a).length >= 3) {
        const {
          hand_is_made,
        } = movePieceFromSrcToDestWhileTakingOpponentPieceIfNeeded(
          game_state,
          msg.data.src,
          msg.data.dest,
          room_info.is_IA_down_for_me,
        );
        game_state.moves_to_be_polled[game_state.season].push({
          byIAOwner: room_info.is_IA_down_for_me,
          move: { type: "NonTamMove", data },
          status: hand_is_made ? "not yet" : null,
        });
      } else {
        game_state.moves_to_be_polled[game_state.season].push({
          byIAOwner: room_info.is_IA_down_for_me,
          move: { type: "NonTamMove", data },
          status: null, // never completes a move
        });
      }
      const ans: RetNormalMove = { type: "WithWaterEntry", ciurl };
      return ans;
    } else {
      const {
        hand_is_made,
      } = movePieceFromSrcToDestWhileTakingOpponentPieceIfNeeded(
        game_state,
        msg.data.src,
        msg.data.dest,
        room_info.is_IA_down_for_me,
      );

      game_state.moves_to_be_polled[game_state.season].push({
        byIAOwner: room_info.is_IA_down_for_me,
        move: {
          type: "NonTamMove",
          data: msg.data,
        },
        status: hand_is_made ? "not yet" : null,
      });

      const ans: RetNormalMove = {
        type: "WithoutWaterEntry"
      };
      return ans;
    }
  } else if (msg.type === "TamMove") {
    setPiece(game_state, msg.src, null);
    setPiece(game_state, msg.secondDest, "Tam2");
    // tam2 can't take

    game_state.moves_to_be_polled[game_state.season].push({
      byIAOwner: room_info.is_IA_down_for_me,
      move: msg,
      status: null, // never completes a hand
    });

    // Tam2 never fails water entry
    const ans: RetNormalMove = {
      type: "WithoutWaterEntry"
    };
    return ans;
  } else {
    let _should_not_reach_here: never = msg;
    throw new Error("should not reach here");
  }
}

function analyzeValidAfterHalfAcceptanceMessageAndUpdate(
  msg: AfterHalfAcceptance,
  room_info: RoomInfoWithPerspective,
): RetAfterHalfAcceptance {
  return analyzeAfterHalfAcceptanceAndUpdate(msg, room_info);
}

function analyzeNormalMoveMessageAndUpdate(
  message: object,
  room_info: RoomInfoWithPerspective,
): RetNormalMove {
  const onLeft = (
    errors: t.Errors,
  ): RetNormalMove => ({
    type: "Err",
    why_illegal: `Invalid message format encountered in analyzeMainMessageAndUpdate(): ${errors.length} error(s) found during parsing ${JSON.stringify(message)}`,
  });

  return pipe(
    NormalMoveVerifier.decode(message),
    fold(onLeft, msg => analyzeValidNormalMoveMessageAndUpdate(msg, room_info)
    ),
  );
}

function analyzeInfAfterStepMessageAndUpdate(
  message: object,
  room_info: RoomInfoWithPerspective,
): RetInfAfterStep {
  const onLeft = (
    errors: t.Errors,
  ): RetInfAfterStep => ({
    type: "Err",
    why_illegal: `Invalid message format encountered in analyzeMainMessageAndUpdate(): ${errors.length} error(s) found during parsing ${JSON.stringify(message)}`,
  });

  return pipe(
    InfAfterStepVerifier.decode(message),
    fold(onLeft, msg => analyzeValidInfAfterStepMessageAndUpdate(msg, room_info)
    ),
  );
}

function analyzeAfterHalfAcceptanceMessageAndUpdate(
  message: object,
  room_info: RoomInfoWithPerspective,
): RetAfterHalfAcceptance {
  const onLeft = (
    errors: t.Errors,
  ): RetAfterHalfAcceptance => ({
    type: "Err",
    why_illegal: `Invalid message format in analyzeAfterHalfAcceptanceMessageAndUpdate(): ${errors.length} error(s) found during parsing ${JSON.stringify(message)}`,
  });

  return pipe(
    AfterHalfAcceptanceVerifier.decode(message),
    fold(onLeft, msg => analyzeValidAfterHalfAcceptanceMessageAndUpdate(msg, room_info)
    ),
  );
}



function decide_who_goes_first(): WhoGoesFirst {
  const process: [Ciurl, Ciurl][] = [];
  while (true) {
    const ciurl1: Ciurl = [Math.random() < 0.5, Math.random() < 0.5, Math.random() < 0.5, Math.random() < 0.5, Math.random() < 0.5];
    const ciurl2: Ciurl = [Math.random() < 0.5, Math.random() < 0.5, Math.random() < 0.5, Math.random() < 0.5, Math.random() < 0.5];
    process.push([ciurl1, ciurl2]);
    if (ciurl1.filter(a => a).length > ciurl2.filter(a => a).length) { return { process, result: true } }
    if (ciurl1.filter(a => a).length < ciurl2.filter(a => a).length) { return { process, result: false } }
  }
}

function swap_who_goes_first(a: WhoGoesFirst): WhoGoesFirst {
  return { result: !a.result, process: a.process.map(([c1, c2]) => [c2, c1]) }
}


const vs_cpu_battle = (() => {
  function vs_cpu_battle_entrance(o: { is_staging: boolean }) {
    return (_req: Request, res: Response) => {
      res.json(vsCpuEntry(o.is_staging));
    }
  }

  function vsCpuEntry(is_staging: boolean): RetVsCpuEntry {
    const newToken: SessionToken = uuidv4() as SessionToken;
    const bot_token: BotToken = uuidv4() as BotToken;

    const room_id = open_a_room_against_bot(bot_token, newToken, is_staging);

    const is_first_turn_newToken_turn: Tuple4<WhoGoesFirst> = [
      decide_who_goes_first(),
      decide_who_goes_first(),
      decide_who_goes_first(),
      decide_who_goes_first(),
    ];

    const is_IA_down_for_newToken = Math.random() < 0.5;

    person_to_fully_occupied_room.set(newToken, {
      room_id,
      is_first_move_my_move: is_first_turn_newToken_turn,
      is_IA_down_for_me: is_IA_down_for_newToken,
    });
    bot_to_room.set(bot_token, {
      room_id,
      is_first_move_my_move: [
        swap_who_goes_first(is_first_turn_newToken_turn[0]),
        swap_who_goes_first(is_first_turn_newToken_turn[1]),
        swap_who_goes_first(is_first_turn_newToken_turn[2]),
        swap_who_goes_first(is_first_turn_newToken_turn[3]),
      ],
      is_IA_down_for_me: !is_IA_down_for_newToken,
    });
    room_to_bot.set(room_id, bot_token);
    room_to_gamestate.set(room_id, {
      tam_itself_is_tam_hue: true,
      season: 0,
      log2_rate: 0,
      IA_owner_s_score: 20,
      is_IA_owner_s_turn:
        is_first_turn_newToken_turn[0 /* spring */].result ===
        is_IA_down_for_newToken,
      f: {
        currentBoard: create_initialized_board(),
        hop1zuo1OfIAOwner: [],
        hop1zuo1OfNonIAOwner: [],
      },
      waiting_for_after_half_acceptance: null,
      moves_to_be_polled: [[], [], [], []],
    });
    console.log(
      `Opened a room ${room_id} to be used by a player ${newToken} and a bot ${bot_token}.`,
    );
    publicly_announce_matching(
      `Opened a room ${sha256_first7(room_id)} to be used by a player ${sha256_first7(newToken)} and a bot ${sha256_first7(bot_token)}.`,
      is_staging
    );

    console.log(
      `${is_first_turn_newToken_turn[0 /* spring */] ? newToken : bot_token
      } moves first.`,
    );
    publicly_announce_matching(
      `${is_first_turn_newToken_turn[0 /* spring */] ? sha256_first7(newToken) : sha256_first7(bot_token)
      } moves first.`,
      is_staging
    );

    console.log(
      `IA is down, from the perspective of ${is_IA_down_for_newToken ? newToken : bot_token
      }.`,
    );
    publicly_announce_matching(
      `IA is down, from the perspective of ${is_IA_down_for_newToken ? sha256_first7(newToken) : sha256_first7(bot_token)
      }.`,
      is_staging
    );

    return {
      type: "LetTheGameBegin",
      session_token: newToken,
      is_first_move_my_move: is_first_turn_newToken_turn[0 /* spring */],
      is_IA_down_for_me: is_IA_down_for_newToken,
    };

  }

  return {
    entrance: vs_cpu_battle_entrance,
  };
})();

function initializeRoomBetweenTwoPeopleAndBegin(o: {
  token: SessionToken, newToken: SessionToken, is_staging: boolean, room_id: RoomId
}): {
  type: "LetTheGameBegin";
  session_token: string;
  is_first_move_my_move: WhoGoesFirst;
  is_IA_down_for_me: boolean;
} {
  const token = o.token;
  const newToken = o.newToken;
  const room_id = o.room_id;
  const is_first_turn_newToken_turn: Tuple4<WhoGoesFirst> = [
    decide_who_goes_first(),
    decide_who_goes_first(),
    decide_who_goes_first(),
    decide_who_goes_first(),
  ];

  const is_IA_down_for_newToken = Math.random() < 0.5;

  person_to_fully_occupied_room.set(newToken, {
    room_id,
    is_first_move_my_move: is_first_turn_newToken_turn,
    is_IA_down_for_me: is_IA_down_for_newToken,
  });
  person_to_fully_occupied_room.set(token, {
    room_id,
    is_first_move_my_move: [
      swap_who_goes_first(is_first_turn_newToken_turn[0]),
      swap_who_goes_first(is_first_turn_newToken_turn[1]),
      swap_who_goes_first(is_first_turn_newToken_turn[2]),
      swap_who_goes_first(is_first_turn_newToken_turn[3]),
    ],
    is_IA_down_for_me: !is_IA_down_for_newToken,
  });
  room_to_gamestate.set(room_id, {
    tam_itself_is_tam_hue: true,
    season: 0,
    log2_rate: 0,
    IA_owner_s_score: 20,
    is_IA_owner_s_turn:
      is_first_turn_newToken_turn[0 /* spring */].result ===
      is_IA_down_for_newToken,
    f: {
      currentBoard: create_initialized_board(),
      hop1zuo1OfIAOwner: [],
      hop1zuo1OfNonIAOwner: [],
    },
    waiting_for_after_half_acceptance: null,
    moves_to_be_polled: [[], [], [], []],
  });
  console.log(
    `Opened a room ${room_id} to be used by ${newToken} and ${token}.`,
  );
  publicly_announce_matching(
    `Opened a room ${sha256_first7(room_id)} to be used by ${sha256_first7(newToken)} and ${sha256_first7(token)}.`,
    o.is_staging
  );

  console.log(
    `${is_first_turn_newToken_turn[0 /* spring */] ? newToken : token
    } moves first.`,
  );
  publicly_announce_matching(
    `${is_first_turn_newToken_turn[0 /* spring */] ? sha256_first7(newToken) : sha256_first7(token)
    } moves first.`,
    o.is_staging
  );

  console.log(
    `IA is down, from the perspective of ${is_IA_down_for_newToken ? newToken : token
    }.`,
  );
  publicly_announce_matching(
    `IA is down, from the perspective of ${is_IA_down_for_newToken ? sha256_first7(newToken) : sha256_first7(token)
    }.`,
    o.is_staging
  );

  return {
    type: "LetTheGameBegin",
    session_token: newToken,
    is_first_move_my_move: is_first_turn_newToken_turn[0 /* spring */],
    is_IA_down_for_me: is_IA_down_for_newToken,
  };
}

const random_battle = (() => {
  const RandomBattlePollVerifier = t.strict({
    session_token: t.string,
  });

  const RandomBattleCancelVerifier = t.strict({
    session_token: t.string,
  });
  function random_battle_poll(o: { is_staging: boolean }) {
    return (req: Request, res: Response) => {
      const onLeft = (errors: t.Errors): RetRandomPoll => ({
        type: "Err",
        why_illegal: `Invalid message format encountered in random_entrance_poll(): ${errors.length} error(s) found during parsing`,
      });

      return res.json(
        pipe(
          RandomBattlePollVerifier.decode(req.body),
          fold(onLeft, function (msg: { session_token: string }): RetRandomPoll {
            const session_token = msg.session_token as SessionToken;
            const maybe_room_id:
              | RoomInfoWithPerspective
              | undefined = person_to_fully_occupied_room.get(session_token);
            if (typeof maybe_room_id !== "undefined") {
              return {
                type: "Ok",
                ret: {
                  type: "LetTheGameBegin",
                  session_token: msg.session_token,
                  is_first_move_my_move:
                    maybe_room_id.is_first_move_my_move[0 /* spring */],
                  is_IA_down_for_me: maybe_room_id.is_IA_down_for_me,
                },
              };
            } else if (random_match_waiting_list.has(session_token)) {
              // not yet assigned a room, but is in the waiting list
              return {
                type: "Ok",
                ret: {
                  type: "InWaitingList",
                  session_token: msg.session_token,
                },
              };
            } else {
              // You sent me a poll, but  I don't know you. Hmm...
              return {
                type: "Err",
                why_illegal: `Invalid session token: 
I don't know ${session_token}, which is the session token that you sent me.
Please reapply by sending an empty object to random/entry .`,
              };

              // FIXME: in the future, I might let you reapply. This will of course change your UUID.
            }
          }),
        ),
      );
    }
  }
  function random_battle_cancel(o: { is_staging: boolean }) {
    return (req: Request, res: Response) => {
      const onLeft = (errors: t.Errors): RetRandomCancel => ({
        type: "Err",
        why_illegal: `Invalid message format: ${errors.length} error(s) found during parsing`,
      });

      return res.json(
        pipe(
          RandomBattleCancelVerifier.decode(req.body),
          fold(onLeft, function (msg: { session_token: string }): RetRandomCancel {
            const session_token = msg.session_token as SessionToken;
            const maybe_room_id:
              | RoomInfoWithPerspective
              | undefined = person_to_fully_occupied_room.get(session_token);

            // you already have a room. you cannot cancel
            if (typeof maybe_room_id !== "undefined") {
              return {
                type: "Ok",
                cancellable: false,
              };
            } else if (random_match_waiting_list.has(session_token)) {
              // not yet assigned a room, but is in the waiting list
              random_match_waiting_list.delete(session_token);
              console.log(`Canceled ${session_token}.`);
              publicly_announce_matching(`Canceled ${sha256_first7(session_token)}. 
            The current waiting list is [${Array.from(random_match_waiting_list.values(), sha256_first7).join(", ")}]`, o.is_staging);
              return {
                type: "Ok",
                cancellable: true,
              };
            } else {
              // You told me to cancel, but I don't know you. Hmm...
              // well, at least you can cancel
              return {
                type: "Ok",
                cancellable: true,
              };
            }
          }),
        ),
      );
    }
  }

  function random_battle_entrance(o: { is_staging: boolean }) {
    return (_req: Request, res: Response) => {
      res.json(randomEntry(o));
    }
  }

  function randomEntry(o: { is_staging: boolean }): RetRandomEntry {
    const newToken: SessionToken = uuidv4() as SessionToken;
    for (let token of random_match_waiting_list) {
      random_match_waiting_list.delete(token);
      publicly_announce_matching(`The current waiting list is [${Array.from(random_match_waiting_list.values(), sha256_first7).join(", ")}]`, o.is_staging);
      console.log("A random match between", token, "and", newToken, "will begin.");
      publicly_announce_matching(`A random match between ${sha256_first7(token)} and ${sha256_first7(newToken)} will begin.`, o.is_staging)
      const room_id = uuidv4() as RoomId
      // exit the loop after finding the first person
      return initializeRoomBetweenTwoPeopleAndBegin({ token, newToken, is_staging: o.is_staging, room_id })
    }

    // If you are still here, that means no one is found
    random_match_waiting_list.add(newToken);
    console.log(
      `Cannot find a partner for ${newToken}, who will thus be put in the waiting list.`,
    );
    publicly_announce_matching(
      `Cannot find a partner for ${sha256_first7(newToken)}, who will thus be put in the waiting list.
      The current waiting list is [${Array.from(random_match_waiting_list.values(), sha256_first7).join(", ")}]`,
      o.is_staging
    );
    return {
      type: "InWaitingList",
      session_token: newToken,
    };
  }

  return {
    entrance: random_battle_entrance,
    poll: random_battle_poll,
    cancel: random_battle_cancel,
  };
})();

const friend_battle = (() => {
  const FriendBattlePollVerifier = t.strict({
    session_token: t.string,
  });

  const FriendJoinRoomVerifier = t.strict({
    room_id: t.string,
    room_key: t.string,
  });

  const FriendDeleteRoomVerifier = t.strict({
    session_token: t.string,
  });

  function vsFriendMakeRoom(is_staging: boolean): RetFriendMakeRoom {
    const session_token = uuidv4() as SessionToken;
    const room_id = uuidv4() as RoomId;
    const room_key = uuidv4() as RoomKey;

    person_to_half_occupied_room.set(session_token, room_id);
    half_occupied_room_to_person.set(room_id, session_token);
    room_to_key.set(room_id, room_key);

    console.log(
      `Opened a room ${room_id} requested by${session_token}.`,
    );

    publicly_announce_matching(
      `Opened a room ${sha256_first7(room_id)} requested by${sha256_first7(session_token)}.
      The current waiting list for the friend match is [${[...person_to_half_occupied_room.entries()].map(([tok, room]) => `${sha256_first7(tok)}: ${sha256_first7(room)}`)
      }]`, is_staging
    )

    return { type: "RoomMade", session_token, room_id, room_key }
  }

  function make_room(o: { is_staging: boolean }) {
    return (_req: Request, res: Response) => {
      res.json(vsFriendMakeRoom(o.is_staging));
    }
  }

  function join_room(o: { is_staging: boolean }) {
    return (req: Request, res: Response) => {
      const onLeft = (errors: t.Errors): RetFriendJoinRoom => ({
        type: "Err",
        why_illegal: `Invalid message format encountered in friend_battle.join_room(): ${errors.length} error(s) found during parsing`,
      });

      return res.json(
        pipe(
          FriendJoinRoomVerifier.decode(req.body),
          fold(onLeft, function (msg: { room_id: string, room_key: string }): RetFriendJoinRoom {
            const room_id = msg.room_id as RoomId;
            const room_key = msg.room_key as RoomKey;
            const expected_room_key: RoomKey | undefined = room_to_key.get(room_id);
            if (expected_room_key === undefined) {
              return { type: "Err", why_illegal: "invalid room id" };
            }
            if (expected_room_key !== room_key) {
              return { type: "Err", why_illegal: "wrong key" };
            }

            const token: SessionToken | undefined = half_occupied_room_to_person.get(room_id);
            if (token === undefined) {
              return { type: "Err", why_illegal: "the room is already occupied" };
            }

            const newToken: SessionToken = uuidv4() as SessionToken;
            console.log("A random match between", token, "and", newToken, "will begin.");
            publicly_announce_matching(`A random match between ${sha256_first7(token)} and ${sha256_first7(newToken)} will begin.`, o.is_staging)

            const ret = initializeRoomBetweenTwoPeopleAndBegin({ token, newToken, is_staging: o.is_staging, room_id });
            return { type: "Ok", ret };
          })
        )
      )
    }
  }

  function delete_room(o: { is_staging: boolean }) {
    return (req: Request, res: Response) => {
      const onLeft = (errors: t.Errors): RetFriendDeleteRoom => ({
        type: "Err",
        why_illegal: `Invalid message format encountered in friend_battle.delete_room(): ${errors.length} error(s) found during parsing`,
      });

      return res.json(
        pipe(
          FriendDeleteRoomVerifier.decode(req.body),
          fold(onLeft, function (msg: { session_token: string }): RetFriendDeleteRoom {
            const session_token = msg.session_token as SessionToken;
            const maybe_room_info:
              | RoomInfoWithPerspective
              | undefined = person_to_fully_occupied_room.get(session_token);

            // The room no longer belongs to you only. Since a friend has joined your room, you cannot delete the room.
            if (typeof maybe_room_info !== "undefined") {
              return {
                type: "Err",
                why_illegal: "The room no longer belongs to you only. Since a friend has joined your room, you cannot delete the room.",
              };
            } else if (person_to_half_occupied_room.has(session_token)) {
              // No one has come to your room, and is in the waiting list
              const room_id = person_to_half_occupied_room.get(session_token)!;
              person_to_half_occupied_room.delete(session_token);
              half_occupied_room_to_person.delete(room_id);
              room_to_key.delete(room_id);
              console.log(`Canceled ${session_token}'s room ${room_id}.`);
              publicly_announce_matching(`Canceled ${sha256_first7(session_token)}'s room ${sha256_first7(room_id)}. 
            The current waiting list for the friend match is [${[...person_to_half_occupied_room.entries()].map(([tok, room]) => `${sha256_first7(tok)}: ${sha256_first7(room)}`)}]`, o.is_staging);
              return {
                type: "Ok",
                ret: "RoomIsRevoked",
              };
            } else {
              // You told me to cancel, but I don't know you. Hmm...
              // well, at least you can cancel
              return {
                type: "Ok",
                ret: "RoomIsRevoked",
              };
            }
          }),
        ),
      );
    }
  }

  // This poll is only called by the one who made the room.
  function poll(o: { is_staging: boolean }) {
    return (req: Request, res: Response) => {
      const onLeft = (errors: t.Errors): RetFriendPoll => ({
        type: "Err",
        why_illegal: `Invalid message format encountered in friend_battle.poll(): ${errors.length} error(s) found during parsing`,
      });

      return res.json(
        pipe(
          FriendBattlePollVerifier.decode(req.body),
          fold(onLeft, function (msg: { session_token: string }): RetFriendPoll {
            const session_token = msg.session_token as SessionToken;
            const maybe_room_id:
              | RoomInfoWithPerspective
              | undefined = person_to_fully_occupied_room.get(session_token);
            if (typeof maybe_room_id !== "undefined") {
              return {
                type: "Ok",
                ret: {
                  type: "LetTheGameBegin",
                  is_first_move_my_move:
                    maybe_room_id.is_first_move_my_move[0 /* spring */],
                  is_IA_down_for_me: maybe_room_id.is_IA_down_for_me,
                },
              };
            } else if (person_to_half_occupied_room.has(session_token)) {
              // in the waiting list
              return {
                type: "Ok",
                ret: {
                  type: "StillAloneInTheRoom",
                },
              };
            } else {
              // You sent me a poll, but  I don't know you. Hmm...
              return {
                type: "Err",
                why_illegal: `Invalid access token: 
I don't know ${session_token}, which is the access token that you sent me.
This API, "/matching/friend/poll", should only be called by the room-maker.
If you want to make a new room, post to "/matching/friend/make_room".`,
              };

              // FIXME: in the future, I might let you reapply. This will of course change your UUID.
            }
          }),
        ),
      );
    }
  }


  return {
    make_room, join_room, delete_room, poll
  }
})();

const app = express();

app.use(bodyParser.urlencoded({ extended: true }));
app.use(bodyParser.json());

app.use(function (req, res, next) {
  res.header("Access-Control-Allow-Origin", "*");
  res.header(
    "Access-Control-Allow-Headers",
    "Origin, X-Requested-With, Content-Type, Accept, Authorization",
  );
  next();
});

app
  .use(express.static(path.join(__dirname, "public")))
  .get("/", (req: Request, res: Response) => res.redirect('https://github.com/sozysozbot/cerke_online_backend'))
  .post("/poll/main", somepoll("/poll/main", replyToMainPoll))
  .post("/poll/inf", somepoll("/poll/inf", replyToInfPoll))
  .post("/decision/tymok", whethertymok_tymok)
  .post("/decision/taxot", whethertymok_taxot)
  .post(
    "/poll/whethertymok",
    somepoll("/poll/whethertymok", replyToWhetherTyMokPoll),
  )
  .post("/decision/normalmove", normalmove)
  .post("/decision/infafterstep", infafterstep)
  .post("/decision/afterhalfacceptance", afterhalfacceptance)
  .post("/matching/random/entry", random_battle.entrance({ is_staging: false }))
  .post("/matching/random/poll", random_battle.poll({ is_staging: false }))
  .post("/matching/random/cancel", random_battle.cancel({ is_staging: false }))
  .post("/matching/random/entry/staging", random_battle.entrance({ is_staging: true }))
  .post("/matching/random/poll/staging", random_battle.poll({ is_staging: true }))
  .post("/matching/random/cancel/staging", random_battle.cancel({ is_staging: true }))
  .post("/matching/vs_cpu/entry", vs_cpu_battle.entrance({ is_staging: false }))
  .post("/matching/vs_cpu/entry/staging", vs_cpu_battle.entrance({ is_staging: true }))
  .post("/matching/friend/make_room", friend_battle.make_room({ is_staging: false }))
  .post("/matching/friend/make_room/staging", friend_battle.make_room({ is_staging: true }))
  .post("/matching/friend/join_room", friend_battle.join_room({ is_staging: false }))
  .post("/matching/friend/join_room/staging", friend_battle.join_room({ is_staging: true }))
  .post("/matching/friend/poll", friend_battle.poll({ is_staging: false }))
  .post("/matching/friend/poll/staging", friend_battle.poll({ is_staging: true }))
  .post("/matching/friend/delete_room", friend_battle.delete_room({ is_staging: false }))
  .post("/matching/friend/delete_room/staging", friend_battle.delete_room({ is_staging: true }))
  .listen(PORT, () => console.log(`Listening on ${PORT}`));

function somepoll<T>(
  address: string,
  replyfn: (room_info: RoomInfoWithPerspective) => T,
) {
  return function (req: Request, res: Response) {
    console.log(`\n sent to '${address}'`);
    console.log(JSON.stringify(req.body, null, "\t"));

    const authorization = req.headers.authorization;
    if (authorization == null) {
      res.json({
        legal: false,
        whyIllegal: "send with `Authorization: Bearer [token]`",
      });
      return;
    } else if (authorization.slice(0, 7) !== "Bearer ") {
      res.json({
        legal: false,
        whyIllegal: "send with `Authorization: Bearer [token]`",
      });
      return;
    }

    const token_ = authorization.slice(7);
    const maybe_room_info = person_to_fully_occupied_room.get(token_ as SessionToken);
    if (typeof maybe_room_info === "undefined") {
      res.json({ type: "Err", why_illegal: "unrecognized user" });
      return;
    }

    console.log("from", req.headers.authorization);
    res.json(replyfn(maybe_room_info));
  };
}

function receiveTyMokAndUpdate(room_info: RoomInfoWithPerspective): RetTyMok {
  const game_state = room_to_gamestate.get(room_info.room_id)!;
  const final_obj = getLastMove(game_state);

  if (typeof final_obj === "undefined") {
    console.log("no last move");
    return { type: "Err", why_illegal: "no last move" };
  }

  if (final_obj.status == null) {
    console.log("no hand");
    return { type: "Err", why_illegal: "no hand" };
  }

  final_obj.status = "ty mok1";
  const log2RateProgressMap: { [P in Log2_Rate]: Log2_Rate } = {
    0: 1,
    1: 2,
    2: 3,
    3: 4,
    4: 5,
    5: 6,
    6: 6, // does not go beyond x64, because the total score is 40
  };
  game_state.log2_rate = log2RateProgressMap[game_state.log2_rate];

  return { type: "Ok" };
}


function receiveTaXotAndUpdate(room_info: RoomInfoWithPerspective): RetTaXot {
  const game_state = room_to_gamestate.get(room_info.room_id)!;
  const final_obj = getLastMove(game_state);

  if (typeof final_obj === "undefined") {
    console.log("no last move");
    return { type: "Err", why_illegal: "no last move" };
  }

  if (final_obj.status == null) {
    console.log("no hand");
    return { type: "Err", why_illegal: "no hand" };
  }

  final_obj.status = "ta xot1";
  if (game_state.season === 3) {
    console.log("the game has ended!");
    return { type: "Ok", is_first_move_my_move: null };
  } else if (game_state.season === 0) {
    game_state.season = 1;
  } else if (game_state.season === 1) {
    game_state.season = 2;
  } else if (game_state.season === 2) {
    game_state.season = 3;
  } else {
    const _should_not_reach_here: never = game_state.season;
    throw new Error("should not happen");
  }

  if (room_info.is_IA_down_for_me) {
    game_state.IA_owner_s_score +=
      calculateHandsAndScore(game_state.f.hop1zuo1OfIAOwner).score *
      Math.pow(2, game_state.log2_rate);
    if (game_state.IA_owner_s_score >= 40) {
      console.log("the game has ended!");
      return { type: "Ok", is_first_move_my_move: null }
    }
  } else {
    game_state.IA_owner_s_score -=
      calculateHandsAndScore(game_state.f.hop1zuo1OfNonIAOwner).score *
      Math.pow(2, game_state.log2_rate);
    if (game_state.IA_owner_s_score < 0) {
      console.log("the game has ended!");
      return { type: "Ok", is_first_move_my_move: null }
    }
  }

  // reset the board
  game_state.f = {
    currentBoard: create_initialized_board(),
    hop1zuo1OfIAOwner: [],
    hop1zuo1OfNonIAOwner: [],
  };

  return {
    type: "Ok",
    is_first_move_my_move:
      room_info.is_first_move_my_move[game_state.season],
  };
}

function whethertymok_tymok(req: Request, res: Response) {
  console.log("\n sent to '/whethertymok/tymok'");
  console.log(JSON.stringify(req.body, null, "\t"));

  const authorization = req.headers.authorization;
  if (authorization == null) {
    res.json({ type: "Err" });
    return;
  } else if (authorization.slice(0, 7) !== "Bearer ") {
    res.json({ type: "Err" });
    return;
  }

  const token_ = authorization.slice(7);
  const maybe_room_info = person_to_fully_occupied_room.get(token_ as SessionToken);
  if (typeof maybe_room_info === "undefined") {
    res.json({ type: "Err" });
    return;
  }

  console.log("from", req.headers.authorization);
  res.json(receiveTyMokAndUpdate(maybe_room_info));
  return;
}

function whethertymok_taxot(req: Request, res: Response) {
  console.log(JSON.stringify(req.body, null, "\t"));

  const authorization = req.headers.authorization;
  if (authorization == null) {
    res.json({ type: "Err" });
    return;
  } else if (authorization.slice(0, 7) !== "Bearer ") {
    res.json({ type: "Err" });
    return;
  }

  const token_ = authorization.slice(7);
  const maybe_room_info = person_to_fully_occupied_room.get(token_ as SessionToken);
  if (typeof maybe_room_info === "undefined") {
    res.json({ type: "Err" });
    return;
  }

  console.log("from", req.headers.authorization);
  const ret = receiveTaXotAndUpdate(maybe_room_info);
  res.json(ret);
  return;
}

function infafterstep(req: Request, res: Response) {
  console.log("\n sent to '/' or '/slow'");
  console.log(JSON.stringify(req.body, null, "\t"));

  const authorization = req.headers.authorization;
  if (authorization == null) {
    res.json({ type: "Err", why_illegal: "send with `Authorization: Bearer [token]`" });
    return;
  } else if (authorization.slice(0, 7) !== "Bearer ") {
    res.json({ type: "Err", why_illegal: "send with `Authorization: Bearer [token]`" });
    return;
  }

  const token_ = authorization.slice(7);
  const maybe_room_info = person_to_fully_occupied_room.get(token_ as SessionToken);
  if (typeof maybe_room_info === "undefined") {
    res.json({ type: "Err", why_illegal: "unrecognized user" });
    return;
  }

  console.log("from", req.headers.authorization);
  let message: unknown = req.body.message;

  if (typeof message !== "object") {
    res.json({ type: "Err", why_illegal: "message is of the primitive type" });
    return;
  }

  if (message == null) {
    res.json({ type: "Err", why_illegal: "no message" });
    return;
  }

  res.json(analyzeInfAfterStepMessageAndUpdate(message, maybe_room_info));
}

function normalmove(req: Request, res: Response) {
  console.log("\n sent to '/' or '/slow'");
  console.log(JSON.stringify(req.body, null, "\t"));

  const authorization = req.headers.authorization;
  if (authorization == null) {
    res.json({ type: "Err", why_illegal: "send with `Authorization: Bearer [token]`" });
    return;
  } else if (authorization.slice(0, 7) !== "Bearer ") {
    res.json({ type: "Err", why_illegal: "send with `Authorization: Bearer [token]`" });
    return;
  }

  const token_ = authorization.slice(7);
  const maybe_room_info = person_to_fully_occupied_room.get(token_ as SessionToken);
  if (typeof maybe_room_info === "undefined") {
    res.json({ type: "Err", why_illegal: "unrecognized user" });
    return;
  }

  console.log("from", req.headers.authorization);
  let message: unknown = req.body.message;

  if (typeof message !== "object") {
    res.json({ type: "Err", why_illegal: "message is of the primitive type" });
    return;
  }

  if (message == null) {
    res.json({ type: "Err", why_illegal: "no message" });
    return;
  }

  res.json(analyzeNormalMoveMessageAndUpdate(message, maybe_room_info));
}

function afterhalfacceptance(req: Request, res: Response) {
  console.log("\n sent to '/decision/afterhalfacceptance'");
  console.log(JSON.stringify(req.body, null, "\t"));

  const authorization = req.headers.authorization;
  if (authorization == null) {
    res.json({ type: "Err", why_illegal: "send with `Authorization: Bearer [token]`" });
    return;
  } else if (authorization.slice(0, 7) !== "Bearer ") {
    res.json({ type: "Err", why_illegal: "send with `Authorization: Bearer [token]`" });
    return;
  }

  const token_ = authorization.slice(7);
  const maybe_room_info = person_to_fully_occupied_room.get(token_ as SessionToken);
  if (typeof maybe_room_info === "undefined") {
    res.json({ type: "Err", why_illegal: "unrecognized user" });
    return;
  }

  console.log("from", req.headers.authorization);
  let message: unknown = req.body.message;

  if (typeof message !== "object") {
    res.json({ type: "Err", why_illegal: "message is of the primitive type" });
    return;
  }

  if (message == null) {
    res.json({ type: "Err", why_illegal: "no message" });
    return;
  }

  res.json(analyzeAfterHalfAcceptanceMessageAndUpdate(message, maybe_room_info));
}

var random_match_waiting_list = new Set<SessionToken>();
var person_to_half_occupied_room = new Map<SessionToken, RoomId>(); // only for friend_battle
var half_occupied_room_to_person = new Map<RoomId, SessionToken>(); // only for friend_battle
var person_to_fully_occupied_room = new Map<SessionToken, RoomInfoWithPerspective>();
var bot_to_room = new Map<BotToken, RoomInfoWithPerspective>();
var room_to_bot = new Map<RoomId, BotToken>(); // only for vs_cpu_battle
var room_to_gamestate = new Map<RoomId, GameState>();
var room_to_key = new Map<RoomId, RoomKey>(); // only for friend_battle


function open_a_room_against_bot(token1: BotToken, token2: SessionToken, is_staging: boolean): RoomId {
  console.log("A match between a bot", token1, "and a player", token2, "will begin.");
  publicly_announce_matching(`A match between a bot ${sha256_first7(token1)} and a player ${sha256_first7(token2)} will begin.`, is_staging)

  // FIXME
  return uuidv4() as RoomId;
}